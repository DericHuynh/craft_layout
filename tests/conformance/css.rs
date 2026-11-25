//! A small parser for the CSS subset used by Taffy's browser-generated fixtures.
//! Values the parser does not recognize become `Value::Other`, which the
//! translator reports as unsupported instead of silently dropping.

use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    Auto,
    Px(f32),
    Percent(f32),
    MaxContent,
    MinContent,
    FitContent,
    Stretch,
    Content,
    Number(f32),
    Other,
}

impl Value {
    pub fn parse(raw: &str) -> Self {
        let raw = raw.trim();
        match raw {
            "auto" | "normal" => return Self::Auto,
            "max-content" => return Self::MaxContent,
            "min-content" => return Self::MinContent,
            "fit-content" => return Self::FitContent,
            "stretch" => return Self::Stretch,
            "content" => return Self::Content,
            _ => {}
        }
        if let Some(px) = raw.strip_suffix("px") {
            return px.parse().map_or(Self::Other, Self::Px);
        }
        if let Some(percent) = raw.strip_suffix('%') {
            return percent.parse::<f32>().map_or(Self::Other, |p| Self::Percent(p / 100.0));
        }
        raw.parse().map_or(Self::Other, Self::Number)
    }
}

/// The attributes of one fixture element, with a record of which ones the
/// translator consumed so the rest can be reported as unsupported.
#[derive(Debug)]
pub struct Style {
    attrs: BTreeMap<String, String>,
    used: std::cell::RefCell<Vec<String>>,
}

impl Style {
    pub fn new(node: roxmltree::Node) -> Self {
        let attrs = node
            .attributes()
            .map(|attribute| (attribute.name().to_string(), attribute.value().trim().to_string()))
            .collect();
        Self { attrs, used: Default::default() }
    }

    /// The raw keyword or value of a property, marking it as handled.
    pub fn get(&self, name: &str) -> Option<&str> {
        let value = self.attrs.get(name)?;
        self.used.borrow_mut().push(name.to_string());
        Some(value.as_str())
    }

    /// The keyword of a property, treating `None` as its CSS initial value.
    pub fn keyword<'a>(&'a self, name: &str, initial: &'a str) -> &'a str {
        self.get(name).unwrap_or(initial)
    }

    pub fn value(&self, name: &str) -> Option<Value> {
        self.get(name).map(Value::parse)
    }

    pub fn number(&self, name: &str, initial: f32) -> Result<f32, String> {
        match self.get(name) {
            None => Ok(initial),
            Some(raw) => raw.parse().map_err(|_| format!("{name}={raw}")),
        }
    }

    /// Properties present on the element that no translation rule read,
    /// ignoring ones whose value equals the CSS initial value.
    pub fn unread(&self) -> Vec<String> {
        let used = self.used.borrow();
        self.attrs
            .iter()
            .filter(|(name, value)| !used.contains(name) && !is_initial(name, value))
            .map(|(name, value)| format!("{name}={value}"))
            .collect()
    }
}

fn is_initial(name: &str, value: &str) -> bool {
    matches!(
        (name, value),
        ("direction", "ltr")
            | ("position", "relative")
            | ("box-sizing", "border-box")
            | ("overflow-x" | "overflow-y", "visible")
            | ("float" | "clear" | "contain", "none")
            | ("scrollbar-width", "0")
            | ("flex-shrink", "1")
            | ("flex-grow", "0")
    )
}
