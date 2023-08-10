use anyhow::{bail, Context};
use serde::Deserialize;
use serde_json::Value;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum BinaryConfigValue {
    Disable,
    #[default]
    Enable,
}

impl From<BinaryConfigValue> for bool {
    fn from(value: BinaryConfigValue) -> Self {
        value == BinaryConfigValue::Enable
    }
}

pub struct Config {
    pub semantic_tokens: bool,
}

impl Config {
    pub fn new(mut value: Value) -> anyhow::Result<Self> {
        let Value::Object(fields) = &mut value else {
            bail!("json::Value is not an object!");
        };

        let semantic_tokens = read_field::<bool>(fields, "semanticTokens")?;

        Ok(Self {
            semantic_tokens: semantic_tokens.into(),
        })
    }
}

fn read_field<T: for<'de> Deserialize<'de>>(
    fields: &mut serde_json::Map<String, Value>,
    name: &str,
) -> anyhow::Result<T> {
    let field = fields
        .remove(name)
        .with_context(|| format!("Expected field config.{name}"))?;

    let typename = std::any::type_name::<T>();
    serde_json::from_value::<T>(field.clone())
        .with_context(|| format!("Expected type {typename}, got {field}"))
}

pub struct Ctx {
    config: Config,
}

impl Ctx {
    pub fn new(config: Config) -> Ctx {
        Ctx { config }
    }
}
