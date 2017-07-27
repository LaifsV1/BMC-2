(* BMC-2 Top Level *)
(*author: Yu-Yang Lin, date: 20/07/2017*)

open AbstractSyntax
open Format
open Lexing
open Translation

let line_sprintf p1 p2 = sprintf "(line %d , col %d) to (line %d , col %d)"
                                 (p1.pos_lnum) (p1.pos_cnum - p1.pos_bol) (p2.pos_lnum) (p2.pos_cnum - p2.pos_bol)

let from_file file = Lexing.from_channel (open_in file);;
let _ =
  try
    (*check for params other than file paths first*)
    if Sys.argv.(1) = "--version" then (printf "    BMC-2 version: 0.0.0.0 \n";exit 0)
    else (
      (*assume param is a file path*)
      print_newline ();
      let file = Sys.argv.(1) in
      printf "    @[***Opening file: %s" file;
      let lexbuf = from_file file in
      printf ".....[done]***";
      close_box ();
      print_newline ();
      try
        printf "    @[***Lexing and Parsing file...";
        let new_parser = Parser.file Lexer.read in
        let new_store,new_meths,new_term = new_parser lexbuf in
        printf ".....[done]*** @]";
        print_newline ();
        printf "    @[***Building initial variables...";
        let new_counter,new_phi = build_cdphi empty_counter True new_store in
        let new_repo = build_repo empty_repo new_meths in
        printf ".....[done]*** @]";
        print_newline ();
        printf "    @[***Running bounded translation...";
        let (_,phi,_,_,_,_) = bmc_translation new_term
                                              new_repo
                                              new_counter
                                              new_counter
                                              new_phi
                                              (nat_of_int 10) in
        printf ".....[done]*** @]";
        print_newline ();
        printf "    OUTPUT FORMULA: %s" (string_of_proposition phi);
        print_newline ();
        printf "    PARSED TERM: %s" (string_of_term new_term);
        print_newline ();
        print_newline ();
        exit 0
      with
      | ParseError (msg,(p1,p2)) -> let tok_error = Lexing.lexeme lexbuf in
                                    printf ".....[error]***@]";
                                    print_newline ();
                                    printf "    @[[PARSE ERROR]:@] @.";
                                    printf "    @[(last token matched): \"%s\"@] @." tok_error;
                                    printf "@[%s@] @." msg;
                                    printf "    @[%s @] @." (line_sprintf p1 p2);
                                    print_newline ();
                                    exit 1
      | SyntaxError (msg,(p1,p2)) -> printf ".....[error]***@]";
                                     print_newline ();
                                     printf "    @[[SYNTAX ERROR]:@] @. ";
                                     printf "@[%s @] @." msg;
                                     printf "    @[%s @] @." (line_sprintf p1 p2);
                                     print_newline ();
                                     exit 1
      | Parser.Error -> printf ".....[error]***@]";
                        print_newline ();
                        printf "    @[[SYNTAX ERROR]: couldn't parse file.@] @. ";
                        print_newline ();
                        exit 1)
  with
  | Sys_error msg -> printf ".....[error]***@]";
                     print_newline ();
                     printf "    @[[SYSTEM ERROR]:@] @.";
                     printf "    @[%s @] @." msg;
                     print_newline ();
                     exit 1
  | e -> Printf.eprintf "    [UNEXPECTED EXCEPTION] : %s \n" (Printexc.to_string e);
         Printf.eprintf "    Usage: \n";
         Printf.eprintf "    Windows: .\\yup.exe <file path> \n";
         Printf.eprintf "    Unix:    ./yup.exe <file path> \n";
         Printf.eprintf "    for version number: ./yup.exe --version \n";
         Printexc.print_backtrace stderr;
         exit 1
