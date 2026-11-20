fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn frame(tag: u8) -> String {
    let mut bytes = 1u16.to_le_bytes().to_vec();
    bytes.push(tag);
    hex(&bytes)
}

fn variants(n: usize) -> String {
    (0..n).map(|i| format!("\n    (V{i})")).collect()
}

pub fn enum256() -> String {
    format!(
        "(program\n  (enum Many{})\n  (decode first Many \"{}\" (value (new V0)))\n  (decode last Many \"{}\" (value (new V255))))\n",
        variants(256),
        frame(0),
        frame(255)
    )
}

pub fn layout_limit() -> String {
    format!("(program\n  (enum Big{}))\n", variants(257))
}

pub fn layout_limit_record() -> String {
    let fields: String = (0..65536).map(|i| format!("\n    (f{i} Int)")).collect();
    format!("(program\n  (record Huge{fields}))\n")
}
