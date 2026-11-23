//! Composition of the production grid assignment and its cached side state.
use super::*;
use grid_search::{SpanCursor, CACHED_SPANS};
use vstd::prelude::*;
use crate::cycles::{self, Event, Storage};
use crate::dependencies::{self, Edge, Part, Source};
use crate::{replay_history, replay_prefix::{self, RootPrefix}};
use crate::replay_view::{self, Replay, ReadWord};
use crate::structural_plan::SubtreeCut;

#[path = "../src/grid_state.rs"]
mod state;

verus! {

pub struct Span {
    pub height: usize,
    pub width: usize,
}

pub struct Snapshot {
    pub cursor: SpanCursor,
    pub occupied: Seq<u64>,
}

impl Snapshot {
    pub open spec fn equal(self, other:Self, stride:usize)->bool {
        let a=self.cursor; let b=other.cursor;
        &&& a.rows==b.rows && a.first_row==b.first_row && a.forward==b.forward
        &&& forall |i:int,j:int| 0<=i<CACHED_SPANS && 0<=j<CACHED_SPANS ==>
            #[trigger] a.limits[i][j]==#[trigger] b.limits[i][j]
        &&& packed(self.occupied,stride as int)==packed(other.occupied,stride as int)
    }

    pub open spec fn empty(self)->bool {
        self.cursor.rows==0 && self.cursor.first_row==0 && self.cursor.forward==(0usize,0usize)
            && (forall|i:int,j:int| 0<=i<CACHED_SPANS && 0<=j<CACHED_SPANS
                ==> #[trigger] self.cursor.limits[i][j]==(0u16,0u16))
            && self.occupied.len()==0
    }

    pub open spec fn place(self, after:Self, cfg:Layout, item:Span, at:(usize,usize))->bool {
        span_step(self.cursor,self.occupied,after.cursor,after.occupied,
            cfg.columns,cfg.stride,item.height,item.width,cfg.backfill,at)
    }
}

pub struct Layout {
    pub columns: usize,
    pub stride: usize,
    pub backfill: bool,
}

proof fn same_start(a:Snapshot,b:Snapshot,cfg:Layout,item:Span)
    requires a.equal(b,cfg.stride), item.height>0, item.width>0,
    ensures span_start(a.cursor.first_row,a.cursor.forward,a.cursor.limits,item.height,item.width,cfg.backfill)
        == span_start(b.cursor.first_row,b.cursor.forward,b.cursor.limits,item.height,item.width,cfg.backfill),
{
    if cfg.backfill {
        let i=vstd::math::min(item.height as int,CACHED_SPANS as int)-1;
        let j=vstd::math::min(item.width as int,CACHED_SPANS as int)-1;
        assert(a.cursor.limits[i][j]==b.cursor.limits[i][j]);
    }
}

/// One invocation of the verified spanned-grid kernel preserves equality of
/// the logical state. The scratch vector's capacity and prior contents outside
/// its used words never enter the width, first-fit, or cursor decisions.
pub proof fn identical_span_step(a:Snapshot,b:Snapshot,an:Snapshot,bn:Snapshot,
    cfg:Layout,item:Span,u:(usize,usize),v:(usize,usize))
    requires a.equal(b,cfg.stride), item.height>0, item.width>0,
        a.place(an,cfg,item,u), b.place(bn,cfg,item,v),
    ensures u==v, an.equal(bn,cfg.stride),
{
    same_start(a,b,cfg,item);
    let start=span_start(a.cursor.first_row,a.cursor.forward,a.cursor.limits,item.height,item.width,cfg.backfill);
    let board=packed(a.occupied,cfg.stride as int);
    let ar=(u.0-a.cursor.first_row,u.1 as int);
    let br=(v.0-b.cursor.first_row,v.1 as int);
    finish_search(board,cfg.columns as int,item.height as int,item.width as int,start,ar,br);
    assert(ar==br && u==v);
    assert forall|i:int,j:int| 0<=i<CACHED_SPANS && 0<=j<CACHED_SPANS implies
        #[trigger] an.cursor.limits[i][j]==#[trigger] bn.cursor.limits[i][j] by {};
}

pub struct Assignment {
    pub states: Seq<Snapshot>,
    pub cells: Seq<(usize,usize)>,
}

impl Assignment {
    pub open spec fn from(self, layout:Layout, items:Seq<Span>)->bool {
        &&& self.states.len()==items.len()+1 && self.cells.len()==items.len()
        &&& self.states[0].empty()
        &&& forall|i:int| 0<=i<items.len() ==> ({
            let s=#[trigger] items[i];
            &&& s.height>0 && s.width>0
            &&& self.states[i].place(self.states[i+1],layout,s,self.cells[i])
        })
    }
}

/// All three numerical kernels are driven by enabled, in-flow children in
/// the same document order. Spanned inputs preserve both physical coordinates
/// and the cross-track count across separately allocated scratch storage.
pub proof fn spanned_assignment_is_deterministic(a:Assignment,b:Assignment,layout:Layout,items:Seq<Span>,n:nat)
    requires a.from(layout,items), b.from(layout,items), n<=items.len(),
    ensures a.states[n as int].equal(b.states[n as int],layout.stride),
        a.cells.take(n as int)==b.cells.take(n as int),
    decreases n,
{
    if n==0 {
        assert(a.states[0].occupied =~= b.states[0].occupied);
    } else {
        let i=n-1;
        spanned_assignment_is_deterministic(a,b,layout,items,i as nat);
        let item=items[i];
        identical_span_step(a.states[i],b.states[i],a.states[n as int],b.states[n as int],
            layout,item,a.cells[i],b.cells[i]);
    }
    assert(a.cells.take(n as int) =~= b.cells.take(n as int));
}

pub enum Run {
    Direct { cursors:Seq<(usize,usize)> },
    Spanned { steps:Assignment },
}

/// Width derived by the runtime is stored verbatim. The same word, converted
/// to usize, drives the otherwise independent integer placement kernel.
pub struct Producer {
    pub key: u32,
    pub binary32_to_columns: spec_fn(u32)->usize,
    pub encode: spec_fn(usize)->u32,
    pub vertical: bool,
    pub items: Seq<Span>,
    pub layout: Layout,
}

impl Producer {
    pub open spec fn has_spans(self)->bool {
        exists|i:int| 0<=i<self.items.len() && ((#[trigger] self.items[i]).height>1
            || self.items[i].width>1)
    }

    pub open spec fn path(self)->state::AssignmentPath {
        state::assignment_path(self.layout.columns,self.items.len() as usize,self.has_spans())
    }

    pub open spec fn clipped_spans(self)->Seq<Span> {
        Seq::new(self.items.len(), |i:int| {
            let span=self.items[i];
            Span { height:span.height,
                width:vstd::math::min(span.width as int,self.layout.columns as int) as usize }
        })
    }

    pub open spec fn direct_next(self, prior:(usize,usize), item:Span)->(usize,usize) {
        if self.path() is OneRow {
            (vstd::math::max(prior.0 as int,item.height as int) as usize,
                (prior.1+item.width) as usize)
        } else if prior.1+1==self.layout.columns {
            ((prior.0+1) as usize,0)
        } else { (prior.0,(prior.1+1) as usize) }
    }

    pub open spec fn observes(self,run:Run)->bool {
        &&& self.layout.columns==(self.binary32_to_columns)(self.key)
        &&& self.layout.columns>0
        &&& self.items.len()<=usize::MAX
        &&& match run {
            Run::Spanned { steps } => self.path() is Search && steps.from(self.layout,self.clipped_spans()),
            Run::Direct { cursors } => {
                &&& !(self.path() is Search)
                &&& cursors.len()==self.items.len()+1
                &&& cursors[0]==(0usize,0usize)
                &&& forall|i:int| 0<=i<self.items.len() ==> cursors[i+1]
                    == self.direct_next(cursors[i],#[trigger] self.items[i])
            },
        }
    }

    pub open spec fn cell(self,run:Run,i:int)->[u32;2] {
        let (row,col)=match run {
            Run::Direct { cursors } => {
                let p=cursors[i];
                if self.path() is OneRow { (0usize,p.1) } else { p }
            },
            Run::Spanned { steps } => steps.cells[i],
        };
        state::physical_pair((self.encode)(col),(self.encode)(row),self.vertical)
    }

    pub open spec fn lines(self,run:Run)->(u32,u32) {
        let rows=match run {
            Run::Direct { cursors } => {
                let end=cursors.last();
                if self.path() is Sequential && end.1!=0 { (end.0+1) as usize } else { end.0 }
            },
            Run::Spanned { steps } => steps.states.last().cursor.rows,
        };
        let physical=state::physical_pair(self.key,(self.encode)(rows),self.vertical);
        (physical[0],physical[1])
    }
}

proof fn direct_prefix(p:Producer,a:Seq<(usize,usize)>,b:Seq<(usize,usize)>,n:nat)
    requires p.observes(Run::Direct {cursors:a}), p.observes(Run::Direct {cursors:b}),
        n<=p.items.len(),
    ensures a[n as int]==b[n as int],
    decreases n,
{
    if n>0 {
        let i=n-1;
        direct_prefix(p,a,b,i as nat);
        assert(a[i+1]==p.direct_next(a[i],p.items[i]));
        assert(b[i+1]==p.direct_next(b[i],p.items[i]));
    }
}

/// Two replays of a grid producer compute the same count words and cell words
/// from the same resolved width, span sequence, axes and immutable local rule.
/// The trace effects are identified by the verified production cursor steps.
pub proof fn initialized_grid_has_unique_words(p:Producer,a:Run,b:Run)
    requires p.observes(a), p.observes(b),
    ensures p.lines(a)==p.lines(b),
        forall|i:int| 0<=i<p.items.len() ==> #[trigger] p.cell(a,i)==#[trigger] p.cell(b,i),
{
    match a {
        Run::Spanned {steps} => {
            let right=b->Spanned_steps;
            let n=p.items.len();
            spanned_assignment_is_deterministic(steps,right,p.layout,p.clipped_spans(),n);
            assert(steps.cells.take(n as int) =~= steps.cells);
            assert(right.cells.take(n as int) =~= right.cells);
        },
        Run::Direct {cursors} => {
            let right=b->Direct_cursors;
            direct_prefix(p,cursors,right,p.items.len());
            assert forall|i:int| 0<=i<p.items.len() implies #[trigger] p.cell(a,i)==#[trigger] p.cell(b,i) by {
                direct_prefix(p,cursors,right,i as nat);
            }
        },
    }
}

pub open spec fn main_word(words:(u32,u32), vertical:bool)->u32 {
    if vertical {words.1} else {words.0}
}

/// An unchanged numeric slot may stop notifying its readers only when its
/// independently re-emitted track words also agree. An exact main word gives
/// the identical discrete search width even past the binary32 integer boundary.
pub proof fn skipped_notification_preserves_assignment(p:Producer,q:Producer,a:Run,b:Run)
    requires
        p.observes(a), q.observes(b), p.items==q.items,
        p.binary32_to_columns==q.binary32_to_columns, p.encode==q.encode,
        p.vertical==q.vertical, p.layout.backfill==q.layout.backfill,
        p.layout.stride == (p.layout.columns+63)/64,
        q.layout.stride == (q.layout.columns+63)/64,
        !state::count_changed(p.lines(a),q.lines(b)),
    ensures p.key==q.key,
        p.lines(a)==q.lines(b),
        forall|i:int| 0<=i<p.items.len() ==> #[trigger] p.cell(a,i)==#[trigger] q.cell(b,i),
{
    assert(main_word(p.lines(a),p.vertical)==p.key);
    assert(main_word(q.lines(b),q.vertical)==q.key);
    assert(p==q);
    initialized_grid_has_unique_words(p,a,b);
}

/// A child rebuilt underneath this unchanged grid restores the physical cell
/// word that a fresh assignment would write. The rest of its sizing data can
/// be cleared independently. Both producer calculations are checked above.
pub proof fn regional_grid_item_keeps_full_cell(p:Producer,a:Run,b:Run,i:int)
    requires p.observes(a), p.observes(b), 0<=i<p.items.len(),
    ensures state::preserve_parent_cell(true,true,p.cell(a,i))==Some(p.cell(b,i)),
{
    initialized_grid_has_unique_words(p,a,b);
}

/// Cross-axis fractional and Fill readers wait for the width-derived counts.
/// A parent estimating its own cross intrinsic size reads the same producer.
/// Both traverse the exact reverse registration edge when the words change.
pub proof fn width_grid_side_readers_receive_notifications(reader:Part,in_flow:bool,
    self_cross:bool)
    requires reader is Declared,
    ensures ({
        let edge=Edge { source:if self_cross {Source::SameNode} else {Source::Parent},
            same_axis:false, in_flow, stack_axis:false, child_has_fill:false,
            grid_main:true, intrinsic_other:false };
        let form=reader->Declared_0;
        &&& dependencies::full_read(reader,Part::Final,edge) == dependencies::notifies(Part::Final,reader,edge)
        &&& dependencies::notifies(Part::Final,reader,edge)
            == if self_cross { form is Intrinsic || form is Ratio } else { in_flow && (form is Fraction || form is Fill) }
    }),
{
    let edge=Edge { source:if self_cross {Source::SameNode} else {Source::Parent},
        same_axis:false, in_flow, stack_axis:false, child_has_fill:false,
        grid_main:true, intrinsic_other:false };
    dependencies::every_read_and_only_reads_are_notified(reader,Part::Final,edge);
    dependencies::declaration_sources(reader->Declared_0,false);
}

/// The width-grid side effect fires after its main Final. In an isolated
/// sizing region, that slot has the same value after the ordered cyclic
/// replay, even if the cross intrinsic calculation read provisional data.
/// Equal regenerated inputs produce exact cell and track words from fresh
/// search scratch. Only the arithmetic decoding of the producer's rule is
/// factored out as a deterministic function of its completed slot bits.
pub proof fn cyclic_width_grid_reemits_full_assignment(r:Replay, main_final:int,
    shape:spec_fn(Seq<u32>)->Producer, a:Run,b:Run)
    requires
        r.closed(), r.inside(main_final),
        shape(r.full_sizing()[main_final]).observes(a),
        shape(r.rebuilt_sizing()[main_final]).observes(b),
    ensures ({
        let full=shape(r.full_sizing()[main_final]);
        let regional=shape(r.rebuilt_sizing()[main_final]);
        &&& full.lines(a)==regional.lines(b)
        &&& forall|i:int| 0<=i<full.items.len() ==> #[trigger] full.cell(a,i)==#[trigger] regional.cell(b,i)
    }),
{
    replay_view::rebuilt_producers_match_the_document(r,main_final);
    initialized_grid_has_unique_words(shape(r.full_sizing()[main_final]),a,b);
}

/// Grid's main Final produces its ordinary scalar, physical X/Y track counts,
/// and the two physical coordinates of each enabled in-flow child in order.
/// These are logical addresses. The runtime keeps the counts in the grid
/// slots and the incoming cell words on each child, with no bundle allocation.
pub enum GridWord {
    MainSize,
    Tracks { y:bool },
    Cell { child:int, y:bool },
}

impl GridWord {
    pub open spec fn offset(self)->int {
        match self {
            Self::MainSize => 0,
            Self::Tracks { y } => if y {2} else {1},
            Self::Cell { child, y } => 3+2*child+if y {1int} else {0int},
        }
    }
    pub open spec fn at(self, producer:int)->ReadWord {
        ReadWord { producer, word:self.offset() }
    }
    pub open spec fn valid(self, items:nat)->bool {
        match self { Self::Cell {child,..} => 0<=child<items, _ => true }
    }
}

pub open spec fn bundle(size:u32, p:Producer, run:Run)->Seq<u32> {
    let lines=p.lines(run);
    Seq::new(3+2*p.items.len(), |i:int| {
        if i==0 { size }
        else if i==1 { lines.0 }
        else if i==2 { lines.1 }
        else { p.cell(run,(i-3)/2)[(i-3)%2] }
    })
}

/// Sizing can read the track on either physical axis. Placement reads both
/// tracks plus its assigned cell. A freely placed child uses none of these.
pub open spec fn placement_reads(producer:int, in_flow_index:Option<int>)->Seq<ReadWord> {
    match in_flow_index {
        None => Seq::empty(),
        Some(child) => seq![
            GridWord::Tracks {y:false}.at(producer), GridWord::Tracks {y:true}.at(producer),
            GridWord::Cell {child,y:false}.at(producer), GridWord::Cell {child,y:true}.at(producer),
        ],
    }
}

pub proof fn physical_side_reads_use_their_own_words(size:u32,p:Producer,run:Run,child:int)
    requires p.observes(run), 0<=child<p.items.len(),
    ensures ({
        let data=bundle(size,p,run);
        &&& data[GridWord::MainSize.offset()]==size
        &&& data[GridWord::Tracks {y:false}.offset()]==p.lines(run).0
        &&& data[GridWord::Tracks {y:true}.offset()]==p.lines(run).1
        &&& data[GridWord::Cell {child,y:false}.offset()]==p.cell(run,child)[0]
        &&& data[GridWord::Cell {child,y:true}.offset()]==p.cell(run,child)[1]
    }),
{
    use vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse;
    lemma_fundamental_div_mod_converse(2*child,2,child,0);
    lemma_fundamental_div_mod_converse(2*child+1,2,child,1);
}

proof fn equivalent_runs_publish_equal_bundles(size:u32,p:Producer,a:Run,b:Run)
    requires p.observes(a), p.observes(b),
    ensures bundle(size,p,a)==bundle(size,p,b),
{
    initialized_grid_has_unique_words(p,a,b);
    assert(bundle(size,p,a) =~= bundle(size,p,b)) by {
        assert forall|i:int| 0<=i<3+2*p.items.len() implies
            bundle(size,p,a)[i]==bundle(size,p,b)[i] by {
            if i>=3 { assert(p.cell(a,(i-3)/2)==p.cell(b,(i-3)/2)); }
        }
    }
}

/// Bind the width Final's evaluator to the grid kernel. The scalar resolver
/// includes the declared bounds. The rule's count and position conversions
/// use the same resolved scalar, padding and spacing as the runtime.
pub struct WidthGrid {
    pub final_slot:int,
    pub resolve:spec_fn(Seq<Seq<u32>>)->u32,
    pub describe:spec_fn(u32)->Producer,
}

impl WidthGrid {
    pub open spec fn finish(self,args:Seq<Seq<u32>>)->Seq<u32> {
        let size=(self.resolve)(args);
        let shape=(self.describe)(size);
        let run=choose |run:Run| shape.observes(run);
        bundle(size,shape,run)
    }

    pub open spec fn installed(self,r:Replay)->bool {
        forall |args:Seq<Seq<u32>>| #[trigger] (r.eval)(self.final_slot,args)==self.finish(args)
    }
}

pub proof fn observed_grid_finishes_with_the_producer_words(grid:WidthGrid,args:Seq<Seq<u32>>,run:Run)
    requires (grid.describe)((grid.resolve)(args)).observes(run),
    ensures grid.finish(args)==bundle((grid.resolve)(args),(grid.describe)((grid.resolve)(args)),run),
{
    let size=(grid.resolve)(args);
    let shape=(grid.describe)(size);
    let selected=choose |candidate:Run| shape.observes(candidate);
    assert(shape.observes(selected));
    equivalent_runs_publish_equal_bundles(size,shape,run,selected);
}

pub open spec fn finish_args(events:Seq<Event>,at:int,initial:Storage,eval:cycles::Compute)->Seq<Seq<u32>> {
    cycles::arguments(events[at].inputs(),cycles::replay(events.take(at),initial,eval))
}

pub open spec fn observes_finish(r:Replay,grid:WidthGrid,events:Seq<Event>,at:int,run:Run)->bool {
    &&& grid.installed(r)
    &&& 0<=at<events.len()
    &&& events[at] is Finish && events[at].target()==grid.final_slot
    &&& forall|i:int| at<i<events.len() ==> (#[trigger] events[i]).target()!=grid.final_slot
    &&& (grid.describe)((grid.resolve)(finish_args(events,at,r.initial,r.eval))).observes(run)
}

proof fn last_finish_publishes_the_grid(r:Replay,grid:WidthGrid,events:Seq<Event>,initial:Storage,at:int,run:Run)
    requires grid.installed(r), 0<=at<events.len(),
        events[at] is Finish, events[at].target()==grid.final_slot,
        forall|i:int| at<i<events.len() ==> (#[trigger] events[i]).target()!=grid.final_slot,
        (grid.describe)((grid.resolve)(finish_args(events,at,initial,r.eval))).observes(run),
    ensures ({
        let args=finish_args(events,at,initial,r.eval);
        let size=(grid.resolve)(args);
        cycles::replay(events,initial,r.eval)[grid.final_slot]==bundle(size,(grid.describe)(size),run)
    }),
    decreases events.len(),
{
    let before=events.drop_last();
    if at<events.len()-1 {
        assert(before.take(at) =~= events.take(at));
        assert(before[at]==events[at]);
        assert forall|i:int| at<i<before.len() implies (#[trigger] before[i]).target()!=grid.final_slot by {
            assert(before[i]==events[i]);
        }
        last_finish_publishes_the_grid(r,grid,before,initial,at,run);
        assert(events.last()==events[events.len()-1]);
    } else {
        assert(events.take(at) =~= before);
        observed_grid_finishes_with_the_producer_words(grid,finish_args(events,at,initial,r.eval),run);
    }
}

/// The typed producer value and the grid's observed physical writes agree.
/// This starts from an observed complete kernel run, then connects it to the
/// exact words read by the inherited frame for this child.
pub proof fn replay_places_the_cells_published_by_the_grid(r:Replay,grid:WidthGrid,
    at:int,run:Run,child:int)
    requires
        r.closed(), r.inside(grid.final_slot), grid.installed(r),
        0<=at<r.full_events().len(), r.full_events()[at] is Finish,
        r.full_events()[at].target()==grid.final_slot,
        forall|i:int| at<i<r.full_events().len() ==> (#[trigger] r.full_events()[i]).target()!=grid.final_slot,
        (grid.describe)((grid.resolve)(finish_args(r.full_events(),at,r.initial,r.eval))).observes(run),
        0<=child<(grid.describe)((grid.resolve)(finish_args(r.full_events(),at,r.initial,r.eval))).items.len(),
    ensures ({
        let args=finish_args(r.full_events(),at,r.initial,r.eval);
        let p=(grid.describe)((grid.resolve)(args));
        let reads=placement_reads(grid.final_slot,Some(child));
        let regional=r.rebuilt_sizing();
        &&& regional[reads[0].producer][reads[0].word]==p.lines(run).0
        &&& regional[reads[1].producer][reads[1].word]==p.lines(run).1
        &&& regional[reads[2].producer][reads[2].word]==p.cell(run,child)[0]
        &&& regional[reads[3].producer][reads[3].word]==p.cell(run,child)[1]
    }),
{
    last_finish_publishes_the_grid(r,grid,r.full_events(),r.initial,at,run);
    replay_view::rebuilt_producers_match_the_document(r,grid.final_slot);
    let size=(grid.resolve)(finish_args(r.full_events(),at,r.initial,r.eval));
    physical_side_reads_use_their_own_words(size,(grid.describe)(size),run,child);
}

/// Carry the exact producer bundle through retained history. Both the track
/// words and per-child cell words can be taken directly from that history.
pub proof fn retained_grid_placement_reads_the_fresh_cells(history:Seq<Replay>,grid:WidthGrid,
    at:int,run:Run,child:int)
    requires replay_history::supported(history), history.len()>0,
        0<=grid.final_slot<history.last().n,
        observes_finish(history.last(),grid,history.last().full_events(),at,run),
        0<=child<(grid.describe)((grid.resolve)(finish_args(
            history.last().full_events(),at,history.last().initial,history.last().eval))).items.len(),
    ensures ({
        let r=history.last();
        let args=finish_args(r.full_events(),at,r.initial,r.eval);
        let p=(grid.describe)((grid.resolve)(args));
        let reads=placement_reads(grid.final_slot,Some(child));
        let retained=replay_history::measured(history);
        &&& retained[reads[0].producer][reads[0].word]==p.lines(run).0
        &&& retained[reads[1].producer][reads[1].word]==p.lines(run).1
        &&& retained[reads[2].producer][reads[2].word]==p.cell(run,child)[0]
        &&& retained[reads[3].producer][reads[3].word]==p.cell(run,child)[1]
    }),
{
    let r=history.last();
    let size=(grid.resolve)(finish_args(r.full_events(),at,r.initial,r.eval));
    last_finish_publishes_the_grid(r,grid,r.full_events(),r.initial,at,run);
    replay_history::every_producer_after_edits_is_exact(history,grid.final_slot);
    physical_side_reads_use_their_own_words(size,(grid.describe)(size),run,child);
}

/// Fresh preparation leaves a Width grid's main Final unresolved so that it
/// can assign tracks on completion. When a fixed-width grid is outside the
/// region and its canonical Finish occurred before the cut, the old producer
/// bundle is already the exact value that the canonical prefix has published.
/// No assumption about equality of the cached counts or cells is necessary.
pub proof fn fixed_width_grid_supplies_the_settled_boundary(
    previous:Replay,cut:RootPrefix,grid:WidthGrid,width:u32,old_at:int,new_at:int,a:Run,b:Run,
)
    requires
        cut.in_order(), !cut.document.inside(grid.final_slot),
        forall |args:Seq<Seq<u32>>| #[trigger] (grid.resolve)(args)==width,
        observes_finish(previous,grid,previous.full_events(),old_at,a),
        observes_finish(cut.document,grid,cut.settled().events,new_at,b),
    ensures previous.full_sizing()[grid.final_slot]==cut.prefix_words()[grid.final_slot],
        cut.prefix_words().contains_key(grid.final_slot),
        (cut.settled().search.state)(grid.final_slot)==cycles::kernel::SOLVED,
{
    let next=cut.document;
    let prefix=cut.settled().events;
    last_finish_publishes_the_grid(previous,grid,previous.full_events(),previous.initial,old_at,a);
    last_finish_publishes_the_grid(next,grid,prefix,next.initial,new_at,b);
    assert((grid.resolve)(finish_args(previous.full_events(),old_at,previous.initial,previous.eval))==width);
    assert((grid.resolve)(finish_args(prefix,new_at,next.initial,next.eval))==width);
    equivalent_runs_publish_equal_bundles(width,(grid.describe)(width),a,b);
    crate::replay_prefix::finished_prefix_slot_is_ready(cut,grid.final_slot,new_at);
}

/// Slot shapes of a retained, non-Block Width grid with two pixel axes and
/// no intrinsic bounds. Its assigned children are visited in a separate
/// region. A parent-side dependency can name either physical Final slot.
pub struct FixedGridCut {
    pub topology: SubtreeCut,
    pub grid: int,
    pub main: int,
    pub cross: int,
    pub part: spec_fn(int) -> Part,
    pub relation: spec_fn(int, int) -> Edge,
}

impl FixedGridCut {
    pub open spec fn describes(self, document: Replay) -> bool {
        &&& self.topology.valid()
        &&& (self.topology.parent)(self.topology.root) == Some(self.grid)
        &&& !self.topology.inside.contains(self.grid)
        &&& (document.owner)(self.main) == self.grid && (document.owner)(self.cross) == self.grid
        &&& forall |n:int| #[trigger] (document.nodes)(n) == self.topology.inside.contains(n)
        &&& forall |slot:int| (#[trigger] (document.owner)(slot)) == self.grid ==> ({
            let part = (self.part)(slot);
            &&& part is Final ==> slot == self.main || slot == self.cross
            &&& part is Final || part is Declared && part->Declared_0 is Constant
        })
        &&& forall |k:int,j:int| 0 <= j < (document.edges)(k).len() ==> ({
            let dep = #[trigger] (document.edges)(k)[j];
            let edge = (self.relation)(k, j);
            document.inside(k) != document.inside(dep) ==> ({
                &&& self.topology.relates((document.owner)(k), (document.owner)(dep), edge)
                &&& dependencies::full_read((self.part)(k), (self.part)(dep), edge)
            })
        })
    }
}

/// The fixed grid has no sizing dispatch into its children. A dependency
/// crossing out of the regional subtree reads one of the grid's two Finals.
pub proof fn fixed_grid_dependencies_cross_only_to_parent_finals(
    boundary: FixedGridCut, document: Replay, k: int, j: int,
)
    requires boundary.describes(document), 0 <= j < (document.edges)(k).len(),
    ensures ({
        let dep = (document.edges)(k)[j];
        &&& !document.inside(k) ==> !document.inside(dep)
        &&& document.inside(k) && !document.inside(dep) ==> dep == boundary.main || dep == boundary.cross
    }),
{
    let dep = (document.edges)(k)[j];
    if document.inside(k) != document.inside(dep) {
        let r = (document.owner)(k);
        let p = (document.owner)(dep);
        let t = boundary.topology;
        let e = (boundary.relation)(k, j);
        assert(t.relates(r, p, e));
        assert(dependencies::full_read((boundary.part)(k), (boundary.part)(dep), e));
        assert(document.inside(k) == t.inside.contains(r));
        assert(document.inside(dep) == t.inside.contains(p));
        if document.inside(k) {
            assert(e.source is Parent);
            assert((t.parent)(r) == Some(p));
            assert(r == t.root);
            assert(p == boundary.grid);
            assert((boundary.part)(dep) is Final || (boundary.part)(dep) is Declared);
            assert((boundary.part)(dep) is Final);
        } else {
            assert(e.source is Child);
            assert((t.parent)(p) == Some(r));
            assert(p == t.root);
            assert(r == boundary.grid);
            assert((boundary.part)(k) is Final || (boundary.part)(k) is Declared
                && (boundary.part)(k)->Declared_0 is Constant);
            assert(!dependencies::full_read((boundary.part)(k), (boundary.part)(dep), e));
        }
    }
}

/// Earlier canonical root requests cannot enter this fixed Grid subtree.
pub proof fn fixed_grid_prefix_leaves_child_region_untouched(boundary: FixedGridCut, cut: RootPrefix)
    requires boundary.describes(cut.document), cut.in_order(),
        forall |i:int| 0 <= i < cut.before().len() ==> ({
            let node = #[trigger] cut.before()[i];
            node.owned_by(cut.document.owner) && !(cut.document.nodes)(node.node)
        }),
    ensures cut.untouched_region(),
{
    let d = cut.document;
    assert forall |k:int,j:int| !d.inside(k) && 0 <= j < (d.edges)(k).len() implies
        !d.inside(#[trigger] (d.edges)(k)[j]) by {
        fixed_grid_dependencies_cross_only_to_parent_finals(boundary,d,k,j);
    }
    crate::planner_boundary::independent_preceding_visits_leave_region_fresh(cut);
}

/// Consume the cached assignment directly in regional placement. The
/// slot shapes and canonical Grid Finish discharge the Grid crossings.
pub proof fn outer_width_grid_reuses_its_cells_in_the_rebuilt_view(
    previous:Replay, cut:RootPrefix, boundary:FixedGridCut, grid:WidthGrid, width:u32,
    old_at:int, grid_visit:int, a:Run, retained:Storage,
    nodes:Seq<replay_view::PlaceNode>, draw:replay_view::Draw,
)
    requires
        cut.in_order(), boundary.describes(cut.document),
        boundary.main == grid.final_slot,
        (cut.document.initial_state)(boundary.main) == cycles::kernel::UNSOLVED,
        (cut.document.initial_state)(boundary.cross) == cycles::kernel::SOLVED,
        0 <= grid_visit < cut.split, ({
            let parent = cut.before()[grid_visit];
            &&& parent.node == boundary.grid
            &&& (parent.x,parent.y) == (boundary.main,boundary.cross)
                || (parent.x,parent.y) == (boundary.cross,boundary.main)
        }),
        forall |args:Seq<Seq<u32>>| #[trigger] (grid.resolve)(args)==width,
        observes_finish(previous,grid,previous.full_events(),old_at,a),
        grid.installed(cut.document),
        retained.contains_key(grid.final_slot), retained[grid.final_slot]==previous.full_sizing()[grid.final_slot],
        forall |i:int| 0 <= i < cut.document.visits.len() ==>
            (#[trigger] cut.document.visits[i]).owned_by(cut.document.owner),
        forall |i:int| 0 <= i < cut.before().len() ==> !(cut.document.nodes)((#[trigger] cut.before()[i]).node),
        forall |k:int| #[trigger] cut.document.inside(k) ==> ({
            let d = cut.document;
            &&& (d.initial_state)(k) == (d.regional_state)(k)
            &&& d.initial.contains_key(k) && retained.contains_key(k) && d.initial[k] == retained[k]
        }),
        forall |k:int| #[trigger] cut.resume(retained).pinned(k) && k!=grid.final_slot ==> (
            cut.prefix_words().contains_key(k) && retained.contains_key(k) && retained[k]==cut.prefix_words()[k]),
        forall |i:int,j:int| 0<=i<nodes.len() && 0<=j<nodes[i].inputs.len() ==> ({
            let k = (#[trigger] nodes[i].inputs[j]).producer;
            cut.document.inside(k) || cut.resume(retained).pinned(k) || k==grid.final_slot
        }),
    ensures cut.resume(retained).closed(),
        replay_view::place_frame(nodes,cut.resume(retained).rebuilt_sizing(),draw)==
            replay_view::place_frame(nodes,cut.document.full_sizing(),draw),
{
    let d = cut.document;
    assert((d.owner)(grid.final_slot) == boundary.grid);
    assert(!(d.nodes)(boundary.grid));
    assert forall |i:int| 0 <= i < cut.before().len() implies ({
        let node = #[trigger] cut.before()[i];
        node.owned_by(d.owner) && !(d.nodes)(node.node)
    }) by { assert(cut.before()[i] == d.visits[i]); }
    fixed_grid_prefix_leaves_child_region_untouched(boundary,cut);
    crate::planner_boundary::parent_finals_are_settled(cut,grid_visit);
    replay_prefix::canonical_ready_has_exact_origin(cut,boundary.main);
    let prefix = cut.settled().events;
    let new_at = choose |i:int| #[trigger] replay_prefix::finished_at(prefix,boundary.main,i);
    replay_prefix::finished_prefix_slot_has_no_later_write(cut,boundary.main,new_at);
    assert((grid.resolve)(finish_args(previous.full_events(),old_at,previous.initial,previous.eval)) == width);
    assert((grid.resolve)(finish_args(prefix,new_at,d.initial,d.eval)) == width);
    assert(observes_finish(d,grid,prefix,new_at,a));
    fixed_width_grid_supplies_the_settled_boundary(previous,cut,grid,width,old_at,new_at,a,a);
    let suffix = cut.resume(retained);
    assert(suffix.pinned(grid.final_slot));
    assert forall |k:int,j:int| 0 <= j < (d.edges)(k).len() implies ({
        let dep = #[trigger] (d.edges)(k)[j];
        let state = cut.settled().search.state;
        &&& !d.inside(k) && d.inside(dep) ==> state(k) == cycles::kernel::SOLVED
        &&& d.inside(k) && !d.inside(dep) ==> state(dep) == cycles::kernel::SOLVED
    }) by {
        fixed_grid_dependencies_cross_only_to_parent_finals(boundary,d,k,j);
    }
    assert forall |k:int| #[trigger] suffix.pinned(k) implies ({
        &&& suffix.initial.contains_key(k) && suffix.cached.contains_key(k)
        &&& suffix.initial[k]==suffix.cached[k]
    }) by {
        if k==grid.final_slot {
            assert(suffix.initial[k]==previous.full_sizing()[k]);
        } else {
            assert(cut.resume(retained).pinned(k));
            assert(retained[k]==cut.prefix_words()[k]);
        }
    }
    crate::replay_prefix::retained_prefix_closes_the_suffix(cut,retained);
    crate::replay_prefix::settled_prefix_rebuilds_the_view(cut,retained,nodes,draw);
}

}
