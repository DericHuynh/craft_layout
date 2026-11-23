//! The same cached measurer runs natively and is checked with Verus.
#![allow(unexpected_cfgs)]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]

#[cfg(not(verus_keep_ghost))]
use keru_layout::measurement as keru_measurement;
#[cfg(verus_keep_ghost)]
use keru_measurement::Model;
use keru_measurement::{Axis, Measurer, Request, SizeBits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

// A widget has precomputed sizes and a height for one particular wrap width.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
struct Widget {
    width: u32,
    height: u32,
    sample_width: u32,
    sample_height: u32,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
struct Entry {
    node: u64,
    content: Widget,
    request: Request,
    size: SizeBits,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct CachedMeasurer {
    entry: Option<Entry>,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns left == right, no_unwind))]
fn same_widget(left: Widget, right: Widget) -> bool {
    left.width == right.width
        && left.height == right.height
        && left.sample_width == right.sample_width
        && left.sample_height == right.sample_height
}

#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns uncached(content, request), no_unwind))]
fn uncached(content: &Widget, request: Request) -> SizeBits {
    let wrap_width = match request {
        Request::TextHeight { wrap_width } => wrap_width,
        Request::Content {
            axis: Axis::Y,
            known_dimensions: [width, _],
            ..
        } => width,
        _ => None,
    };
    let height = match wrap_width {
        Some(width) if width == content.sample_width => content.sample_height,
        _ => content.height,
    };
    SizeBits {
        x: content.width,
        y: height,
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    impl Model<u64, Widget> for CachedMeasurer {
        closed spec fn cache_valid(&self) -> bool {
            match self.entry {
                Some(entry) => entry.size == Self::expected(entry.node, &entry.content, entry.request),
                None => true,
            }
        }

        closed spec fn expected(_node: u64, content: &Widget, request: Request) -> SizeBits {
            uncached(content, request)
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl CachedMeasurer {
    #[cfg_attr(verus_keep_ghost, verus_spec(cache => ensures cache.cache_valid()))]
    fn new() -> Self {
        Self { entry: None }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Measurer<u64, Widget> for CachedMeasurer {
    fn measure(&mut self, node: u64, content: &Widget, request: Request) -> SizeBits {
        match self.entry {
            Some(entry)
                if entry.node == node
                    && same_widget(entry.content, *content)
                    && entry.request.same_input(&request) =>
            {
                entry.size
            }
            _ => {
                let size = uncached(content, request);
                self.entry = Some(Entry {
                    node,
                    content: *content,
                    request,
                    size,
                });
                size
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    // The initial cache states can differ and both calls use the real method.
    fn independent_caches_agree(
        a: &mut CachedMeasurer, b: &mut CachedMeasurer,
        node: u64, content: &Widget, request: Request,
    ) -> (outputs: (SizeBits, SizeBits))
        requires old(a).cache_valid(), old(b).cache_valid(),
        ensures final(a).cache_valid(), final(b).cache_valid(), outputs.0 == outputs.1,
        no_unwind
    {
        (a.measure(node, content, request), b.measure(node, content, request))
    }
}

#[cfg(not(verus_keep_ghost))]
fn main() {
    let mut measurer = CachedMeasurer::new();
    // An exact sample key makes the distinction between +0 and -0 observable.
    let content = Widget {
        width: 40.0_f32.to_bits(),
        height: 12.0_f32.to_bits(),
        sample_width: (-0.0_f32).to_bits(),
        sample_height: 24.0_f32.to_bits(),
    };
    let positive = Request::text_height(Some(0.0));
    let negative = Request::text_height(Some(-0.0));
    assert_eq!(measurer.measure(0, &content, positive).y, content.height);
    assert_eq!(
        measurer.measure(0, &content, negative).y,
        content.sample_height
    );
    assert_eq!(
        measurer.measure(0, &content, negative).y,
        content.sample_height
    );

    #[cfg(feature = "incremental")]
    {
        use keru_layout::{ContentMeasure, LayoutParams, LayoutTree, Pos, Size, Xy};
        let mut tree = LayoutTree::new();
        let widget = tree.add_node_with_context(
            &tree.root(),
            LayoutParams {
                size: Xy::new(Size::Pixels(20.0), Size::FitContent),
                position: Xy::new_symm(Pos::Start),
                content_measure: ContentMeasure::HeightForWidth,
                ..LayoutParams::DEFAULT
            },
            Widget {
                sample_width: 20.0_f32.to_bits(),
                ..content
            },
        ).unwrap();
        tree.solve_layout_with_content_measure(Xy::new(100.0, 100.0), |_, context, input| {
            measurer
                .measure(1, context.expect("widget content"), input.into())
                .to_size()
        });
        assert_eq!(tree.layout(&widget).unwrap().y, [0.0, 24.0]);
    }
}
