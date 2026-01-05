use wasm_bindgen::prelude::*;
use spartan_vm_interpreter::{
    interpreter, ConstraintsLayout, Field, WitnessLayout,
};
use ark_ff::BigInteger;
use acir_field::AcirField;

// Use wee_alloc as the global allocator for smaller WASM binary and better memory management
#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

macro_rules! console_log {
    ($($t:tt)*) => (log(&format_args!($($t)*).to_string()))
}

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
        console_log!("WasmInterpreter initialized");
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

        console_log!("Loaded witgen bytecode: {} u64s", bytecode.len());
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

        console_log!("Loaded AD bytecode: {} u64s", bytecode.len());
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

        console_log!("Loaded layouts - witness size: {}, constraints size: {}",
            witness_layout.size(), constraints_layout.size());

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

        console_log!("Running witgen with {} inputs {:?}", flat_inputs.len(), flat_inputs);

        // For now, we need to convert flat inputs to InputValue format
        // This is a temporary workaround - we'll need the actual InputValue conversion
        // For simple cases with just field inputs, we can create a vec of Field InputValues
        use noirc_abi::input_parser::InputValue;
        use acir_field::FieldElement;

        console_log!("Converting inputs to InputValue format...");
        let input_values: Vec<InputValue> = flat_inputs
            .iter()
            .map(|f| {
                let fe = FieldElement::from_be_bytes_reduce(&f.0.to_bytes_be());
                InputValue::Field(fe)
            })
            .collect();

        console_log!("Starting branching interpreter...");
        console_log!("Bytecode size: {} u64s", bytecode.len());
        console_log!("Witness layout size: {}", witness_layout.size());
        console_log!("Constraints layout size: {}", constraints_layout.size());
        console_log!("Input values: {:?}", input_values);

        let result = interpreter::run_branching(
            bytecode,
            *witness_layout,
            *constraints_layout,
            &input_values,
        );

        console_log!("Interpreter completed successfully!");

        // Convert result to JSON
        let output = serde_json::json!({
            "witness_pre_comm": result.out_wit_pre_comm.iter()
                .map(|f| f.0.to_string())
                .collect::<Vec<_>>(),
            "witness_post_comm": result.out_wit_post_comm.iter()
                .map(|f| f.0.to_string())
                .collect::<Vec<_>>(),
            "a": result.out_a.iter()
                .map(|f| f.0.to_string())
                .collect::<Vec<_>>(),
            "b": result.out_b.iter()
                .map(|f| f.0.to_string())
                .collect::<Vec<_>>(),
            "c": result.out_c.iter()
                .map(|f| f.0.to_string())
                .collect::<Vec<_>>(),
        });

        Ok(serde_wasm_bindgen::to_value(&output)?)
    }
}
