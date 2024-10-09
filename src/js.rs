use self_cell::self_cell;
use wasm_bindgen::prelude::*;

use crate::architecture::Architecture;

mod utils;

self_cell!(
    /// Architecture description
    #[wasm_bindgen]
    pub struct ArchitectureJS {
        owner: String,
        #[covariant]
        dependent: Architecture,
    }
);

#[wasm_bindgen]
#[allow(clippy::use_self)] // wasm_bindgen doesn't support using `Self` on nested types
impl ArchitectureJS {
    /// Load architecture data from `JSON`
    ///
    /// # Parameters
    ///
    /// * `src`: `JSON` data to deserialize
    ///
    /// # Errors
    ///
    /// Errors if the input `JSON` data is invalid, either because it's ill-formatted or because it
    /// doesn't conform to the specification
    pub fn from_json(json: String) -> Result<ArchitectureJS, String> {
        utils::set_panic_hook();
        Self::try_new(json, |json| Architecture::from_json(json)).map_err(|e| e.to_string())
    }

    #[wasm_bindgen(js_name = toString)]
    #[must_use]
    pub fn debug(&self) -> String {
        format!("{:#?}", self.borrow_dependent())
    }

    pub fn compile(&self, src: &str) -> Result<(), String> {
        // TODO: properly print errors and return result
        let ast = crate::parser::parse(src).map_err(|e| format!("{e:#?}"))?;
        let _ = crate::compiler::compile(self.borrow_dependent(), ast)
            .map_err(|e| format!("{e:#?}"))?;
        todo!()
    }
}
