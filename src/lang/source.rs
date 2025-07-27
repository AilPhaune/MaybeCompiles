pub struct SourceFile {
    name: String,
    contents: String,
    byte_len: usize,
}

impl SourceFile {
    pub fn new(name: String, contents: String) -> SourceFile {
        SourceFile {
            name,
            byte_len: contents.len(),
            contents,
        }
    }

    pub fn get_contents(&self) -> &str {
        &self.contents
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn get_byte_len(&self) -> usize {
        self.byte_len
    }
}
