{
  open AbstractSyntax
  open Parser
  open Lexing

  let next_line lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <-
      { pos with
        Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
        Lexing.pos_bol = pos.Lexing.pos_cnum;
      }

  let lex_failure (msg : string) (pos1 : position) (pos2 : position) =
    SyntaxError (("error lexing "^ msg),(pos1,pos2))
}

let name = ['a'-'z']['A'-'Z''a'-'z''0'-'9''_''\'']*
let int = '-'? ['0'-'9'] ['0'-'9']*
let open_comment = "(*"
let close_comment = "*)"
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read = parse
  | white           { read lexbuf }
  | newline         { next_line lexbuf; read lexbuf }
  | '('             { OPEN_PAREN }
  | ')'             { CLOSE_PAREN }
  | ','             { COMMA }
  | ':'             { COLON }
  | ';'             { SEMICOLON }
  | "Int"           { Integer_TYPE }
  | "Unit"          { Unit_TYPE }
  | "->"            { ARROW_OP }
  | '*'             { TIMES_OP }
  | '+'             { PLUS_OP }
  | ">="            { GTE_OP }
  | "fail"          { Fail_TERM }
  | "skip"          { Skip_TERM }
  | int as i        { Int_TERM (int_of_string i) }
  | "fun"           { Lambda_TERM }
  | "!"             { Deref_TERM_OP }
  | "fst"           { Left_TERM_OP }
  | "snd"           { Right_TERM_OP }
  | ":="            { Assign_TERM_OP }
  | "="             { EQUALS_OP }
  | "let"           { Let_TERM }
  | "in"            { In_TERM }
  | "if"            { If_TERM }
  | "then"          { Then_TERM }
  | "else"          { Else_TERM }
  | "Pair"          { PAIR_OP }
  | "Methods"       { METHOD }
  | "Store"         { STORE }
  | "Main"          { MAIN }
  | name as x       { NAME x }
  | eof             { EOF }
  | open_comment    { comment lexbuf }
  | _               { raise (lex_failure ("unknown symbol '"^(lexeme lexbuf)^"'") (lexeme_start_p lexbuf) (lexeme_end_p lexbuf)) }
and comment = parse
  | close_comment   { read lexbuf }
  | newline         { next_line lexbuf; comment lexbuf }
  | _               { comment lexbuf }
{
}
