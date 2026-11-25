use super::*;
use std::fmt::Write;
use std::path::Path;

fn escape(text: &str) -> String {
    text.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
}

fn surface(key: &str) -> Option<&'static str> {
    Some(match key {
        "screen" | "left" | "right" => "#171c27",
        "title" | "rail" | "terminal" => "#101520",
        "explorer" | "inspector" => "#202735",
        "tabs" | "crumb" => "#242d3d",
        "tab-current" | "file-current" => "#33435b",
        "divider" => "#526176",
        "status" => "#284c5c",
        _ => return None,
    })
}

fn ink(key: &str) -> &'static str {
    match key {
        "problem" | "command-output" => "#f1b491",
        "project" | "tab-current" | "file-current" | "branch" => "#9de4dc",
        key if key.ends_with("-number") || key.ends_with("-title") => "#94a5c0",
        key if key.ends_with("-code") => "#d3def2",
        _ => "#bfcbda",
    }
}

pub(super) fn write(path: &Path, s: Session, view: &View, rects: &Rects) -> std::io::Result<()> {
    let mut out = format!(r#"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {} {}" font-family="monospace" font-size="13"><title>Keystone editor workbench</title>"#, s.width, s.height);
    for n in &view.0 {
        let Some(r) = rects[&n.key] else { continue };
        let [x, end_x] = r.x;
        let [y, end_y] = r.y;
        let w = end_x - x;
        let h = end_y - y;
        if let Some(fill) = surface(&n.key) {
            writeln!(out, r#"<rect x="{x}" y="{y}" width="{w}" height="{h}" fill="{fill}"/>"#).unwrap();
        }
        if let Some(text) = &n.text {
            let [pl, pr] = n.params.padding.x;
            let [pt, _] = n.params.padding.y;
            let wrap = (n.params.text == TextContent::Wrapping).then_some(w-pl-pr);
            let id = &n.key;
            let color = ink(id);
            writeln!(out, r#"<clipPath id="clip-{id}"><rect x="{x}" y="{y}" width="{w}" height="{h}"/></clipPath><g clip-path="url(#clip-{id})">"#).unwrap();
            for (i, line) in lines(text, wrap).into_iter().enumerate() {
                let baseline = y + pt + 12.0 + i as f32 * LINE;
                let length = line.chars().count() as f32 * CHAR;
                if length > 0.0 {
                    writeln!(out, r#"<text x="{}" y="{baseline}" fill="{color}" xml:space="preserve" textLength="{length}" lengthAdjust="spacingAndGlyphs">{}</text>"#, x+pl, escape(&line)).unwrap();
                }
            }
            out.push_str("</g>\n");
        }
    }
    out.push_str("</svg>\n");
    std::fs::write(path, out)
}
