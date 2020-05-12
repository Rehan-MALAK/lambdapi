open Format

(* VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVv *)
let print_option f fmt = function
  | None -> fprintf fmt "None"
  | Some x -> f fmt x

let print_option_or_default default f fmt = function
  | None -> fprintf fmt "%s" default
  | Some x -> f fmt x
(* VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVv *)
let rec print_list_pre sep print fmt = function
  | [] -> ()
  | x :: r -> sep fmt (); print fmt x; print_list_pre sep print fmt r

let rec print_list_suf sep print fmt = function
  | [] -> ()
  | x :: r -> print fmt x; sep fmt (); print_list_suf sep print fmt r

let print_list sep print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; print_list_pre sep print fmt r

let print_list_or_default default sep print fmt = function
  | [] -> fprintf fmt "%s" default
  | l -> print_list sep print fmt l

let print_list_par sep pr fmt l =
  print_list sep (fun fmt x -> fprintf fmt "(%a)" pr x) fmt l

let print_list_delim ~start ~stop ~sep pr fmt = function
  | [] -> ()
  | l -> fprintf fmt "%a%a%a" start () (print_list sep pr) l stop ()

let print_list_next sep print fmt = function
  | [] -> ()
  | [x] -> print true fmt x
  | x :: r ->
      print true fmt x; sep fmt ();
      print_list sep (print false) fmt r
(* VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVv *)
(* from ocaml/testsuite/tests/lib-bigarray/change_layout *)
let pp_sep ppf () = Format.fprintf ppf ";@ "
let print_array pp ppf a =
  Format.fprintf ppf "@[<hov>[|%a|]@]"
    Format.(pp_print_list ~pp_sep pp) (Array.to_list a)
(* VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVv *)
let dot fmt () = fprintf fmt ".@ "
let comma fmt () = fprintf fmt ",@ "
let star fmt () = fprintf fmt "*@ "
let simple_comma fmt () = fprintf fmt ", "
let underscore fmt () = fprintf fmt "_"
let slash fmt () = fprintf fmt "/"
let semi fmt () = fprintf fmt ";@ "
let colon fmt () = fprintf fmt ":@ "
let space fmt () = fprintf fmt "@ "
let alt fmt () = fprintf fmt "|@ "
let alt2 fmt () = fprintf fmt "@ | "
let equal fmt () = fprintf fmt "@ =@ "
let newline fmt () = fprintf fmt "@\n"
let newline2 fmt () = fprintf fmt "@\n@\n"
let arrow fmt () = fprintf fmt "@ -> "
let lbrace fmt () = fprintf fmt "{"
let rbrace fmt () = fprintf fmt "}"
let lsquare fmt () = fprintf fmt "["
let rsquare fmt () = fprintf fmt "]"
let lparen fmt () = fprintf fmt "("
let rparen fmt () = fprintf fmt ")"
let lchevron fmt () = fprintf fmt "<"
let rchevron fmt () = fprintf fmt ">"
let nothing _fmt _ = ()
(*
In ocaml stdlib format :
pp_print_string
pp_print_float
pp_print_int
   ...
*)
(* VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVv *)

let print_pos fmt (a_pos : Pos.pos) =
  ignore a_pos ;
  fprintf fmt "pos"

let print_name s = "\"" ^ s ^ "\""

let print_bindlib_var fmt (var : 'a Bindlib.var) =
  fprintf fmt "%s%d" (print_name var.var_prefix) var.var_suffix

let print_bindlib_mvar fmt (var : 'a Bindlib.mvar) =
  fprintf fmt "%a" (print_array print_bindlib_var) var

let print_name_binded name binded =
  (print_name name) ^ (if binded then " binded" else "" )

let print_bindlib_binder fmt (binder : ('a,'b) Bindlib.binder) =
  fprintf fmt "%s #FV=%d" (print_name_binded binder.b_name binder.b_bind) binder.b_rank

let print_bindlib_mbinder fmt (mbinder : ('a,'b) Bindlib.mbinder) =
  let array_binded = Array.map2 print_name_binded mbinder.mb_names mbinder.mb_binds in
  fprintf fmt "%a #FV=%d" (print_array pp_print_string) array_binded mbinder.mb_rank

let rec print_term fmt (a_pos : Terms.term) =
  match a_pos with
  | Vari term_var -> fprintf fmt "Vari(%a)" print_bindlib_var term_var
  | Type -> fprintf fmt "Type"
  | Kind -> fprintf fmt "Kind"
  | Symb(sym) -> fprintf fmt "Symb(%a)" print_sym sym (*print_pp_hint pp_hint*)
(* NOT ALLOWED IN OCAMLDEBUG
  | Prod(term,term_term_binder) -> let (_,unbinded_term) = Bindlib.unbind term_term_binder in
      fprintf fmt "Prod(%a,binder %a,%a)" print_term term print_bindlib_binder term_term_binder print_term unbinded_term
*)
  | Prod(term,term_term_binder) ->
      fprintf fmt "Prod(%a,binder %a)" print_term term print_bindlib_binder term_term_binder
(* NOT ALLOWED IN OCAMLDEBUG
  | Abst(term,term_term_binder) -> let (_,unbinded_term) = Bindlib.unbind term_term_binder in
      fprintf fmt "Abst(%a,binder %a,%a)" print_term term print_bindlib_binder term_term_binder print_term unbinded_term
*)
  | Abst(term,term_term_binder) ->
      fprintf fmt "Abst(%a,binder %a)" print_term term print_bindlib_binder term_term_binder
  | Appl(term1,term2) -> fprintf fmt "Appl(%a,%a)" print_term term1 print_term term2
  | Meta(meta,term_array) -> fprintf fmt "Meta(%a,%a)" print_meta meta (print_array print_term) term_array
  | Patt(int_option,name,term_array) -> fprintf fmt "Patt(%a,%s,%a)" (print_option pp_print_int) int_option name (print_array print_term) term_array
  | TEnv(term_env,term_array) -> fprintf fmt "TEnv(%a,%a)" print_terms_env term_env (print_array print_term) term_array
  | Wild -> fprintf fmt "Wild"
  | TRef _term_option_ref -> fprintf fmt "TRef"
(* NOT ALLOWED IN OCAMLDEBUG
  | LLet(term1,term2,term_term_binder) -> let (_,unbinded_term) = Bindlib.unbind term_term_binder in
      fprintf fmt "LLet(%a,%a,binder %a,%a)" print_term term1 print_term term2 print_bindlib_binder term_term_binder print_term unbinded_term
   *)
  | LLet(term1,term2,term_term_binder) ->
      fprintf fmt "LLet(%a,%a,binder %a)" print_term term1 print_term term2 print_bindlib_binder term_term_binder

and print_sym fmt (a_sym : Terms.sym) =
(*   fprintf fmt "%s : %a" (print_name a_sym.sym_name) print_term (Timed.(!)(a_sym.sym_type)) *)
  fprintf fmt "%s" (print_name a_sym.sym_name)

and print_meta fmt (a_meta : Terms.meta) =
  let a_meta_deref = Timed.(!) a_meta.meta_value in
  fprintf fmt "\"%a\" : %a,arity:%d,value:%a" (print_option pp_print_string) a_meta.meta_name print_term (Timed.(!)(a_meta.meta_type)) a_meta.meta_arity (print_option print_bindlib_mbinder) a_meta_deref
(* NOT ALLOWED IN OCAMLDEBUG
  let a_meta_deref = Timed.(!) a_meta.meta_value in
  let a_meta_deref_deoption_unbinded = match a_meta_deref with
  | Some x -> let (_,unmbinded_term) = Bindlib.unmbind x in Some unmbinded_term
  | None -> None
  in
  fprintf fmt "\"%a\",arity:%d,value binder:%a,value:%a" (print_option pp_print_string) a_meta.meta_name a_meta.meta_arity (print_option print_bindlib_mbinder) a_meta_deref (print_option print_term) a_meta_deref_deoption_unbinded
*)

(*
and print_pp_hint fmt (a_pp_hint : Terms.pp_hint) =
  match a_pp_hint with
  | Nothing -> fprintf fmt "Nothing"
  | Qualified -> fprintf fmt "Qualified"
  | Alias a_string -> fprintf fmt "Alias %s" a_string
  | Binary a_string -> fprintf fmt "Binary %s" a_string
  | Unary a_string -> fprintf fmt "Unary %s" a_string
*)

and print_terms_env fmt (a_term_env : Terms.term_env) =
 match a_term_env with
  | TE_Vari term_env_bindlib_var -> fprintf fmt "TE_Vari(%a)" print_bindlib_var term_env_bindlib_var
  | TE_Some(term_term_mbinder) ->
(* NOT ALLOWED IN OCAMLDEBUG
      let (_,unmbinded_term) = Bindlib.unmbind term_term_mbinder in
      fprintf fmt "TE_Some(%a,binder %a)" print_term unmbinded_term print_bindlib_mbinder term_term_mbinder
*)
      fprintf fmt "TE_Some(binder %a)" print_bindlib_mbinder term_term_mbinder
  | TE_None -> fprintf fmt "TE_None"

(*
(* specialization *)
let print_bindlib_mvar fmt (var : Terms.term_env Bindlib.mvar) =
  fprintf fmt "%a %a%d" print_terms_env var (print_array print_bindlib_var) var

(* specialization *)
let print_terms_terms_bindlib_mbinder fmt (mbinder : (Terms.term_env,Terms.term) Bindlib.mbinder) =
  let tvar,t = Bindlib.unmbind mbinder in
  let array_binded = Array.map2 print_name_binded mbinder.mb_names mbinder.mb_binds in
  fprintf fmt "tvar:%a t:%a %a #FV=%d" (print_array print_bindlib_var) tvar print_term t (print_array pp_print_string) array_binded mbinder.mb_rank
*)

let print_rule fmt (a_rule : Terms.rule) =
  let print_name_arity fmt _ = fprintf fmt "term_env Bindlib.var TODO" in
(* NOT ALLOWED IN OCAMLDEBUG
  let (_,rhs) = Bindlib.unmbind a_rule.rhs in
  fprintf fmt "@\nlhs :@\n            %a@\nrhs mbinder:@\n            %a@\nrhs :@\n            %a@\narity :@\n          %d@\nvars bound rhs :@\n         %a" (print_list comma print_term) a_rule.lhs print_bindlib_mbinder a_rule.rhs print_term rhs a_rule.arity (print_array pp_print_int) a_rule.arities (print_array print_name_arity) a_rule.vars
*)
  fprintf fmt "@\nlhs :@\n            %a@\nrhs mbinder:@\n            %a@\narity :@\n          %d@\narities :@\n          %a@\nvars bound rhs :@\n         %a" (print_list comma print_term) a_rule.lhs print_bindlib_mbinder a_rule.rhs a_rule.arity (print_array pp_print_int) a_rule.arities (print_array print_name_arity) a_rule.vars

(* print_pos removes most of the verbosity but we can do even better on chosen instanciated polymorphic types *)
let print_term_pos fmt (a_term_pos : Terms.term Pos.loc) =
  fprintf fmt "%a" print_term a_term_pos.elt

let print_rule_pos fmt (a_rule_pos : Terms.rule Pos.loc) =
  fprintf fmt "%a" print_rule a_rule_pos.elt
