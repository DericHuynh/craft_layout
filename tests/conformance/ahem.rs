//! Text measurement matching Taffy's fixture measurer
//! (`taffy/tests/common/src/lib.rs`, `AhemTextMeasureData`): every glyph is a
//! 10 px square, and line breaks are only allowed at zero-width spaces.

const ZWS: char = '\u{200B}';
const GLYPH: f32 = 10.0;

#[derive(Debug, Clone)]
pub struct AhemText {
    /// Byte length of each unbreakable run.
    runs: Vec<usize>,
}

impl AhemText {
    pub fn can_wrap(text: &str) -> bool {
        text.contains(ZWS)
    }

    pub fn new(text: &str) -> Self {
        Self { runs: text.split(ZWS).map(str::len).collect() }
    }

    fn min_line(&self) -> usize {
        self.runs.iter().copied().max().unwrap_or(0)
    }

    fn max_line(&self) -> usize {
        self.runs.iter().sum()
    }

    /// Width without wrapping, as the max-content contribution.
    pub fn max_content_width(&self) -> f32 {
        self.max_line() as f32 * GLYPH
    }

    /// Width of the longest unbreakable run, as the min-content contribution.
    pub fn min_content_width(&self) -> f32 {
        self.min_line() as f32 * GLYPH
    }

    /// The used inline size and block size when wrapping at `available` width.
    pub fn wrap(&self, available: f32) -> (f32, f32) {
        let inline = available.min(self.max_content_width()).max(self.min_content_width());
        let per_line = (inline / GLYPH).floor() as usize;
        let mut lines = 1;
        let mut current = 0;
        for &run in &self.runs {
            if current + run > per_line {
                if current > 0 {
                    lines += 1;
                }
                current = run;
            } else {
                current += run;
            }
        }
        (inline, lines as f32 * GLYPH)
    }
}
