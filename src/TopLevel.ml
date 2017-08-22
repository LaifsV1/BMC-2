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
        let (new_store,new_meths,new_term),main_tp = new_parser lexbuf in (*get decl from parsing*)
        printf ".....[done]*** @]";
        print_newline ();
        printf "    @[***Building initial variables...";
        let new_counter,new_phi,cd_decl = build_cdphi empty_counter True new_store [] in (*get decl from initial counters*)
        let new_repo = build_repo empty_repo new_meths in
        printf ".....[done]*** @]";
        print_newline ();
        printf "    @[***Running bounded translation...";
        let (oret,ophi,oR,oC,oD,oq,odecl) = bmc_translation new_term (*get refs decl from translation*)
                                                            new_repo
                                                            new_counter
                                                            new_counter
                                                            new_phi
                                                            (nat_of_int 10)
                                                            main_tp
                                                            cd_decl in
        (*let oRdecl = repo_get_decl oR odecl in (*get decl from output repo*) (*can't get from repo cuz they strings*)*)
        let def_decl = decl_of_list "" get_default_decl in (*write decl from defaul_decl*)
        let all_decl = decl_of_list def_decl odecl in  (*write decl from everything ontop of default decl*)
        printf ".....[done]*** @]";
        print_newline ();
        print_newline ();
        printf "    SMT-LIB FILE:";
        print_newline ();
        printf "%s" z3_default_type;
        print_newline ();
        print_newline ();
        printf "%s" all_decl;
        print_newline ();
        printf "(assert %s)" (z3_of_proposition ophi);
        print_newline ();
        print_newline ();
        printf "(check-sat)\n(get-model)";
        print_newline ();
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
         Printexc.print_backtrace stderr;
         exit 1
