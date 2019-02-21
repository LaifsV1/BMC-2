(* BMC-2 Top Level *)
(*author: Yu-Yang Lin, date: 20/07/2017*)

open AbstractSyntax
open Format
open Lexing
open Translation

let line_sprintf p1 p2 = sprintf "(line %d , col %d) to (line %d , col %d)"
                                 (p1.pos_lnum) (p1.pos_cnum - p1.pos_bol) (p2.pos_lnum) (p2.pos_cnum - p2.pos_bol)

let debug = ref true
let timing = ref true
let assertfail = ref true

let time f x s =
    let t = Sys.time() in
    let fx = f x in
    if !timing then Printf.printf "\n;;    %s: %fs\n" s (Sys.time() -. t);
    fx

let print_custom_ops () = printf "(define-fun gte ((x Int) (y Int)) Int (if (>= x y) 1 0))\n";
                          printf "(define-fun lte ((x Int) (y Int)) Int (if (<= x y) 1 0))\n";
                          printf "(define-fun eq ((x Int) (y Int)) Int (if (= x y) 1 0))\n";
                          printf "(define-fun and_int ((x Int) (y Int)) Int (if (or (= x 0) (= y 0)) 0 1))\n";
                          printf "(define-fun or_int ((x Int) (y Int)) Int (if (or (not (= x 0)) (not (= y 0))) 1 0))\n"

let from_file file = Lexing.from_channel (open_in file);;
let _ =
  let main_body () =
  try
    (*check for params other than file paths first*)
    if Sys.argv.(1) = "--version" then (printf "    BMC-2 version: 0.0.0.0 \n";exit 0)
    else (
      (*assume param is a file path*)
      print_newline ();
      let file = Sys.argv.(1) in
      let bound = int_of_string (Sys.argv.(2)) in
      if !debug then printf ";;    @[***Opening file: %s" file;
      let lexbuf = from_file file in
      if !debug then printf ".....[done]***";
      close_box ();
      if !debug then print_newline ();
      try
        if !debug then printf ";;    @[***Lexing and Parsing file...";
        let new_parser = Parser.file Lexer.read in
        let (new_store,new_meths,new_term,init_decl,main_args,init_args_neq_fail_nil),main_tp = time new_parser lexbuf "PARSER" in (*get decl from parsing*)
        let fresh_args,fresh_main_phi,new_init_decl = z3_create_fresh_inputs fresh_x init_decl [] True init_decl in
        (*^^^ freshen main inputs. added fresh type declarations into init_decl. REMEMBER: substitute in the term.*)
        let new_term = untyped_subslist new_term fresh_args main_args in
        (*^^^ substituted main inputs for fresh main inputs. REMEMBER: add (old = fresh) assertions.*)
        if !debug then printf ".....[done]*** @]\n";
        if !debug then printf ";;    @[***Building initial variables...";
        let new_counter,new_phi,cd_decl = build_cdphi empty_counter fresh_main_phi new_store new_init_decl in
        (*^^^ get decl from initial counters. added fresh main inputs into new_phi.*)
        let new_repo = build_repo empty_repo new_meths in
        if !debug then printf ".....[done]*** @]";
        if !debug then print_newline ();
        if !debug then printf ";;    @[***Running bounded translation...";
        let (oret,ophi,oR,oC,oD,oq,odecl,oa,opt) = time (bmc_translation new_term (*get refs decl from translation*)
                                                                         new_repo
                                                                         new_counter
                                                                         new_counter
                                                                         new_phi
                                                                         (Suc(nat_of_int bound))
                                                                         main_tp
                                                                         cd_decl)
                                                           empty_ptsmap "BOUNDED TRANSLATION" in
        (*let oRdecl = repo_get_decl oR odecl in (*get decl from output repo*) (*can't get from repo cuz they strings*)*)
        let def_decl = decl_of_list "" get_default_decl in (*write decl from defaul_decl*)
        let all_decl = decl_of_list def_decl odecl in  (*write decl from everything ontop of default decl*)
        if !debug then printf ".....[done]*** @]";
        if !debug then print_newline ();
        if !debug then printf ";;    PARSED TERM: %s\n" (string_of_term new_term);
        if !debug then print_newline ();
        (* if !debug then printf ";;    PROPOSITIONAL FORMULA: %s\n" (string_of_proposition ophi); *)
        (* if !debug then print_newline (); *)
        if !debug then printf ";;    SMT-LIB FILE:";
        if !debug then print_newline ();
        printf "%s\n" z3_default_type;
        print_custom_ops ();
        print_newline ();
        time (printf "%s\n") all_decl "GENERATING TYPE DECLARATIONS";
        printf "%s\n" (z3_assertions_of_list init_args_neq_fail_nil);
        printf "%s\n" (z3_assertions_of_list (get_fail_neq_nil ()));
        printf "%s\n" (z3_assertions_of_list (time get_global_types () "GENERATING ASSERTIONS FOR COMPLEX TYPES"));
        time print_z3_assertion (print_z3_of_proposition,ophi) "GENERATING PROGRAM FORMULA";
        if !assertfail then printf "(assert (= _ret_1_ %s))" (z3_fail_of_tp main_tp);
        print_newline ();
        print_newline ();
        printf "(check-sat)\n;;(get-model)\n";
        z3_getval_of_decl init_decl;
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
  in time main_body () "TOTAL EXECUTION TIME";exit 0
