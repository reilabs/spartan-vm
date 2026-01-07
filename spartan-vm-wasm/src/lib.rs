use wasm_bindgen::prelude::*;
use spartan_vm_interpreter::{
    interpreter, ConstraintsLayout, Field, WitnessLayout,
};
use ark_ff::BigInteger;
use acir_field::AcirField;
use std::sync::Once;
use tracing_subscriber::prelude::*;
use tracing_subscriber_wasm::MakeConsoleWriter;

// Use wee_alloc as the global allocator for smaller WASM binary and better memory management
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

static TRACING_INIT: Once = Once::new();

#[wasm_bindgen]
pub struct WasmInterpreter {
    witgen_bytecode: Option<Vec<u64>>,
    ad_bytecode: Option<Vec<u64>>,
    witness_layout: Option<WitnessLayout>,
    constraints_layout: Option<ConstraintsLayout>,
}

#[wasm_bindgen]
impl WasmInterpreter {
    #[wasm_bindgen(constructor)]
    pub fn new() -> WasmInterpreter {
        console_error_panic_hook::set_once();

        // Initialize tracing to output to console (works in both browser and Node.js)
        TRACING_INIT.call_once(|| {
            use tracing_subscriber::fmt::format::FmtSpan;

            let fmt_layer = tracing_subscriber::fmt::layer()
                .with_ansi(false)
                .without_time()
                // Note: Can't use FmtSpan::CLOSE as it requires std::time::Instant which isn't available in WASM
                .with_span_events(FmtSpan::NEW | FmtSpan::ENTER | FmtSpan::EXIT)
                .with_writer(MakeConsoleWriter::default());

            tracing_subscriber::registry()
                .with(fmt_layer)
                .init();
        });

        tracing::info!("WasmInterpreter initialized");
        WasmInterpreter {
            witgen_bytecode: None,
            ad_bytecode: None,
            witness_layout: None,
            constraints_layout: None,
        }
    }

    #[wasm_bindgen]
    pub fn load_witgen_bytecode(&mut self, bytes: &[u8]) -> Result<(), JsValue> {
        if bytes.len() % 8 != 0 {
            return Err(JsValue::from_str("Bytecode size must be multiple of 8"));
        }

        let mut bytecode = Vec::with_capacity(bytes.len() / 8);
        for chunk in bytes.chunks_exact(8) {
            let value = u64::from_le_bytes(chunk.try_into().unwrap());
            bytecode.push(value);
        }

        tracing::info!(size = bytecode.len(), "Loaded witgen bytecode");
        self.witgen_bytecode = Some(bytecode);
        Ok(())
    }

    #[wasm_bindgen]
    pub fn load_ad_bytecode(&mut self, bytes: &[u8]) -> Result<(), JsValue> {
        if bytes.len() % 8 != 0 {
            return Err(JsValue::from_str("Bytecode size must be multiple of 8"));
        }

        let mut bytecode = Vec::with_capacity(bytes.len() / 8);
        for chunk in bytes.chunks_exact(8) {
            let value = u64::from_le_bytes(chunk.try_into().unwrap());
            bytecode.push(value);
        }

        tracing::info!(size = bytecode.len(), "Loaded AD bytecode");
        self.ad_bytecode = Some(bytecode);
        Ok(())
    }

    #[wasm_bindgen]
    pub fn load_layouts(&mut self, layout_json: &str) -> Result<(), JsValue> {
        let layouts: serde_json::Value = serde_json::from_str(layout_json)
            .map_err(|e| JsValue::from_str(&format!("Failed to parse layouts JSON: {}", e)))?;

        let witness_layout: WitnessLayout =
            serde_json::from_value(layouts["witness"].clone())
                .map_err(|e| JsValue::from_str(&format!("Failed to parse witness layout: {}", e)))?;

        let constraints_layout: ConstraintsLayout =
            serde_json::from_value(layouts["constraints"].clone())
                .map_err(|e| JsValue::from_str(&format!("Failed to parse constraints layout: {}", e)))?;

        tracing::info!(
            witness_size = witness_layout.size(),
            constraints_size = constraints_layout.size(),
            "Loaded layouts"
        );

        self.witness_layout = Some(witness_layout);
        self.constraints_layout = Some(constraints_layout);
        Ok(())
    }

    #[wasm_bindgen]
    pub fn execute_witgen(&self, inputs_json: &str) -> Result<JsValue, JsValue> {
        let bytecode = self
            .witgen_bytecode
            .as_ref()
            .ok_or_else(|| JsValue::from_str("Witgen bytecode not loaded"))?;

        let witness_layout = self
            .witness_layout
            .as_ref()
            .ok_or_else(|| JsValue::from_str("Layouts not loaded"))?;

        let constraints_layout = self
            .constraints_layout
            .as_ref()
            .ok_or_else(|| JsValue::from_str("Layouts not loaded"))?;

        // Parse inputs as flat array of field elements (as strings)
        let inputs: Vec<String> = serde_json::from_str(inputs_json)
            .map_err(|e| JsValue::from_str(&format!("Failed to parse inputs: {}", e)))?;

        // Convert string representations to Field elements
        let flat_inputs: Vec<Field> = inputs
            .iter()
            .map(|s| {
                // Parse as decimal string
                let bigint = ark_ff::BigInt::<4>::try_from(
                    num_bigint::BigUint::parse_bytes(s.as_bytes(), 10)
                        .ok_or_else(|| JsValue::from_str(&format!("Invalid field element: {}", s)))?,
                )
                .map_err(|_| JsValue::from_str("Field element too large"))?;
                Ok(Field::new_unchecked(bigint))
            })
            .collect::<Result<Vec<_>, JsValue>>()?;

        tracing::info!(num_inputs = flat_inputs.len(), "Running witgen");

        // Convert flat inputs to InputValue format
        use noirc_abi::input_parser::InputValue;
        use acir_field::FieldElement;

        let input_values: Vec<InputValue> = flat_inputs
            .iter()
            .map(|f| {
                let fe = FieldElement::from_be_bytes_reduce(&f.0.to_bytes_be());
                InputValue::Field(fe)
            })
            .collect();

        let start_time = js_sys::Date::now();
        let _result = interpreter::run_branching(
            bytecode,
            *witness_layout,
            *constraints_layout,
            &input_values,
        );
        let execution_time_ms = js_sys::Date::now() - start_time;

        tracing::info!(execution_time_ms = execution_time_ms, "Interpreter completed");

        let output = serde_json::json!({
            "execution_time_ms": execution_time_ms,
        });

        Ok(serde_wasm_bindgen::to_value(&output)?)
    }
}
