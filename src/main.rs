use crate::lang::{
    builtins::{bool_module::BooleanModule, int_module::SignedIntegerModule},
    lexer::Lexer,
    parser::Parser,
    source::SourceFile,
    types::TypeCheckingContext,
};

pub mod lang;

/*

Hey compiler, when i say exit with exitcode as i64 i mean:
I would like to syscall 60 and exitcode.
Done.

*/

fn main() {
    let program = SourceFile::new(
        "program.maybecompiles".to_string(),
        r#"

Hey compiler, the program starts here.
Take 0, then call it result.
Do {
    Take result, then use print on it, then discard it, then use add on it with just 1, then call it result.
} until result is equal to 10.
Done.

        "#
        .to_string(),
    );

    println!("Lexing program:");
    println!("{}", program.get_contents().trim());
    println!();

    let mut lexer = Lexer::new(program);
    let state = lexer.push();

    println!("Begin tokens stream\n");
    let mut i = 0;
    while let Some(token) = lexer.next_token() {
        println!("{i:3}: {:?}", token);
        i += 1;
    }
    println!("\nEnd tokens stream");
    println!();

    lexer.pop(state);

    let mut parser = Parser::new(lexer.collect());

    let expr = parser.parse_main_function_declaration().unwrap();

    println!("Parsed tree:\n");
    println!("{:#?}", expr);
    println!("\nEnd parsing");
    println!();

    let i64_module = SignedIntegerModule::create(64).unwrap();
    let bool_module = BooleanModule::new();

    let mut type_checking_context =
        TypeCheckingContext::new_with_builtins(vec![&i64_module, &bool_module]);

    let ir = type_checking_context.construct_ir_declaration(expr.result);

    println!("Begin Type Checking Context Dump\n");
    println!("{:#?}", type_checking_context);
    println!("\nEnd Type Checking Context Dump");
    println!();

    let ir = ir.unwrap();

    println!("IR:\n");
    println!("{:#?}", ir);
    println!("\nEnd IR");
}
