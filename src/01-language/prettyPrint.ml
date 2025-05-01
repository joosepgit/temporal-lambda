open Ast
module Print = Utils.Print
module Symbol = Utils.Symbol

(* Unicode subscripts for digits 0–9 *)
let subscript i =
  let digits =
    [|
      "\226\130\128";
      "\226\130\129";
      "\226\130\130";
      "\226\130\131";
      "\226\130\132";
      "\226\130\133";
      "\226\130\134";
      "\226\130\135";
      "\226\130\136";
      "\226\130\137";
    |]
  in
  let rec build_subscript n =
    if n < 10 then digits.(n) else build_subscript (n / 10) ^ digits.(n mod 10)
  in
  build_subscript i

(* Greek letters for type variables *)
let greek_letters =
  [|
    "α";
    "β";
    "γ";
    "δ";
    "ε";
    "ζ";
    "η";
    "θ";
    "ι";
    "κ";
    "λ";
    "μ";
    "ν";
    "ξ";
    "ο";
    "π";
    "ρ";
    "σ";
  |]

let type_symbol n =
  if n < Array.length greek_letters then greek_letters.(n)
  else "σ" ^ subscript (n - Array.length greek_letters)

let tau_symbol n = "τ" ^ subscript n

module MakeParamPrinter
    (ParamMap : Map.S)
    (SymbolGen : sig
      val symbol_for_index : int -> string
    end) =
struct
  let create () =
    let names = ref ParamMap.empty in
    let counter = ref 0 in
    fun param ppf ->
      let symbol =
        match ParamMap.find_opt param !names with
        | Some sym -> sym
        | None ->
            let sym = SymbolGen.symbol_for_index !counter in
            incr counter;
            names := ParamMap.add param sym !names;
            sym
      in
      Format.fprintf ppf "%s" symbol
end

module TyPrintParam =
  MakeParamPrinter
    (TyParamMap)
    (struct
      let symbol_for_index = type_symbol
    end)

module TauPrintParam =
  MakeParamPrinter
    (TauParamMap)
    (struct
      let symbol_for_index = tau_symbol
    end)

let print_ty_params ty_pp ty_params ppf =
  Format.fprintf ppf "[";
  let rec print_helper = function
    | [] -> ()
    | [ last ] -> Format.fprintf ppf "%t" (ty_pp last)
    | hd :: tl ->
        Format.fprintf ppf "%t, " (ty_pp hd);
        print_helper tl
  in
  print_helper ty_params;
  Format.fprintf ppf "]"

let print_tau_params ?max_level:_ tau_pp tau_params ppf =
  Format.fprintf ppf "[";
  let rec print_helper = function
    | [] -> ()
    | [ last ] -> Format.fprintf ppf "%t" (tau_pp last)
    | hd :: tl ->
        Format.fprintf ppf "%t, " (tau_pp hd);
        print_helper tl
  in
  print_helper tau_params;
  Format.fprintf ppf "]"

let rec print_tau ?max_level:_ tau_pp tau ppf =
  match tau with
  | TauConst i -> Format.fprintf ppf "%d" i
  | TauParam p -> Format.fprintf ppf "%t" (tau_pp p)
  | TauAdd (t1, t2) ->
      Format.fprintf ppf "@[%t + %t@]"
        (fun ppf -> print_tau tau_pp t1 ppf)
        (fun ppf -> print_tau tau_pp t2 ppf)

let rec print_ty ?max_level ty_print_param tau_print_param p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | TyConst c -> print "%t" (Const.print_ty c)
  | TyApply (ty_name, []) -> print "%t" (TyName.print ty_name)
  | TyApply (ty_name, [ ty ]) ->
      print ~at_level:1 "%t %t"
        (print_ty ~max_level:1 ty_print_param tau_print_param ty)
        (TyName.print ty_name)
  | TyApply (ty_name, tys) ->
      print ~at_level:1 "%t %t"
        (Print.print_tuple (print_ty ty_print_param tau_print_param) tys)
        (TyName.print ty_name)
  | TyParam a -> print "%t" (ty_print_param a)
  | TyArrow (ty1, CompTy (ty2, TauConst 0)) ->
      print ~at_level:3 "(%t → %t)"
        (print_ty ~max_level:2 ty_print_param tau_print_param ty1)
        (print_ty ~max_level:3 ty_print_param tau_print_param ty2)
  | TyArrow (ty1, CompTy (ty2, tau)) ->
      print ~at_level:3 "(%t → %t # %t)"
        (print_ty ~max_level:2 ty_print_param tau_print_param ty1)
        (print_ty ~max_level:3 ty_print_param tau_print_param ty2)
        (print_tau tau_print_param tau)
  | TyTuple [] -> print "unit"
  | TyTuple tys ->
      print ~at_level:2 "%t"
        (Print.print_sequence " × "
           (print_ty ~max_level:1 ty_print_param tau_print_param)
           tys)
  | TyBox (tau, ty) ->
      print ~at_level:1 "[%t]%t"
        (print_tau tau_print_param tau)
        (print_ty ~max_level:0 ty_print_param tau_print_param ty)

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | PVar x -> print "%t" (Variable.print x)
  | PAs (p, x) -> print "%t as %t" (print_pattern p) (Variable.print x)
  | PAnnotated (p, _ty) -> print_pattern ?max_level p ppf
  | PConst c -> Const.print c ppf
  | PTuple lst -> Print.print_tuple print_pattern lst ppf
  | PVariant (lbl, None) when lbl = nil_label -> print "[]"
  | PVariant (lbl, None) -> print "%t" (Label.print lbl)
  | PVariant (lbl, Some (PTuple [ v1; v2 ])) when lbl = cons_label ->
      print "%t::%t" (print_pattern v1) (print_pattern v2)
  | PVariant (lbl, Some p) ->
      print ~at_level:1 "%t @[<hov>%t@]" (Label.print lbl) (print_pattern p)
  | PNonbinding -> print "_"

let rec print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e with
  | Var x -> print "%t" (Variable.print x)
  | Const c -> print "%t" (Const.print c)
  | Annotated (t, _ty) -> print_expression ?max_level t ppf
  | Tuple lst -> Print.print_tuple print_expression lst ppf
  | Variant (lbl, None) when lbl = nil_label -> print "[]"
  | Variant (lbl, None) -> print "%t" (Label.print lbl)
  | Variant (lbl, Some (Tuple [ v1; v2 ])) when lbl = cons_label ->
      print ~at_level:1 "%t::%t"
        (print_expression ~max_level:0 v1)
        (print_expression ~max_level:1 v2)
  | Variant (lbl, Some e) ->
      print ~at_level:1 "%t @[<hov>%t@]" (Label.print lbl)
        (print_expression ~max_level:0 e)
  | Lambda a -> print ~at_level:2 "fun %t" (print_abstraction a)
  | PureLambda a -> print ~at_level:2 "fun %t" (print_abstraction a)
  | RecLambda (f, _ty) -> print ~at_level:2 "rec %t ..." (Variable.print f)

and print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | Return e -> print ~at_level:1 "return %t" (print_expression ~max_level:0 e)
  | Do (c1, (PNonbinding, c2)) ->
      print "@[<hov>%t;@ %t@]" (print_computation c1) (print_computation c2)
  | Do (c1, (pat, c2)) ->
      print "@[<hov>let@[<hov>@ %t =@ %t@] in@ %t@]" (print_pattern pat)
        (print_computation c1) (print_computation c2)
  | Match (e, lst) ->
      print "match %t with (@[<hov>%t@])" (print_expression e)
        (Print.print_sequence " | " print_case lst)
  | Apply (e1, e2) ->
      print ~at_level:1 "@[%t@ %t@]"
        (print_expression ~max_level:1 e1)
        (print_expression ~max_level:0 e2)
  | Delay (tau, c) ->
      let print_param = TauPrintParam.create () in
      print ~at_level:1 "delay %t %t"
        (print_tau print_param tau)
        (print_computation c)
  | Box (tau, e, (p, c)) ->
      let print_param = TauPrintParam.create () in
      print ~at_level:1 "box %t[%t] as %t in %t"
        (print_tau print_param tau)
        (print_expression e) (print_pattern p) (print_computation c)
  | Unbox (tau, e, (p, c)) ->
      let print_param = TauPrintParam.create () in
      print ~at_level:1 "unbox %t[%t] as %t in %t"
        (print_tau print_param tau)
        (print_expression e) (print_pattern p) (print_computation c)

and print_abstraction (p, c) ppf =
  Format.fprintf ppf "%t ↦ %t" (print_pattern p) (print_computation c)

and print_case a ppf = Format.fprintf ppf "%t" (print_abstraction a)

let print_vars_and_tys print_var_and_ty lst ppf =
  let rec print_list lst ppf =
    match lst with
    | [] -> ()
    | VarMap map :: rest ->
        Print.print ppf "VarMap: {\n";
        let elements = VariableMap.bindings map in
        let rec print_elements = function
          | [] -> ()
          | entry :: tl ->
              let ty_pp = TyPrintParam.create () in
              let tau_pp = TauPrintParam.create () in
              print_var_and_ty ty_pp tau_pp entry ppf;
              Print.print ppf "\n";
              print_elements tl
        in
        print_elements elements;
        Print.print ppf "}\n";
        print_list rest ppf
    | Tau n :: rest ->
        let tau_pp = TauPrintParam.create () in
        print_tau tau_pp n ppf;
        Print.print ppf "\n";
        print_list rest ppf
  in
  Print.print ppf "VariableContext: [\n";
  print_list (List.rev lst) ppf;
  Print.print ppf "]\n"

let print_vars_and_exprs print_var_and_expr lst ppf =
  let rec print_list lst ppf =
    match lst with
    | [] -> ()
    | VarMap map :: rest ->
        Print.print ppf "{";
        let elements = VariableMap.bindings map in
        let rec print_elements = function
          | [] -> ()
          | entry :: [] -> print_var_and_expr entry ppf
          | entry :: tl ->
              print_var_and_expr entry ppf;
              Print.print ppf ", ";
              print_elements tl
        in
        print_elements elements;
        Print.print ppf "}, ";
        print_list rest ppf
    | Tau n :: [] ->
        let tau_pp = TauPrintParam.create () in
        print_tau tau_pp n ppf
    | Tau n :: rest ->
        let tau_pp = TauPrintParam.create () in
        print_tau tau_pp n ppf;
        Print.print ppf ", ";
        print_list rest ppf
  in
  Print.print ppf "State: [";
  print_list (List.rev lst) ppf;
  Print.print ppf "]\n"

let print_variable_context ctx =
  let print_var_and_ty ty_pp tau_pp (variable, (ty_params, tau_params, ty)) ppf
      =
    Variable.print variable ppf;
    Format.fprintf ppf " -> ";
    print_ty_params ty_pp ty_params ppf;
    Format.fprintf ppf ", ";
    print_tau_params tau_pp tau_params ppf;
    Format.fprintf ppf " ";
    Format.fprintf ppf "@[%t@]" (print_ty ty_pp tau_pp ty);
    Format.pp_print_flush ppf ()
  in
  print_vars_and_tys print_var_and_ty ctx

let print_interpreter_state ctx ppf =
  let print_var_and_expr (variable, (tau, expr)) ppf =
    let tau_print_param = TauPrintParam.create () in
    Format.fprintf ppf "%t -> %t # %t" (Variable.print variable)
      (print_expression expr)
      (print_tau tau_print_param tau)
  in
  print_vars_and_exprs print_var_and_expr ctx ppf

let string_of_interpreter_state context =
  print_interpreter_state context Format.str_formatter;
  Format.flush_str_formatter ()

let string_of_expression e =
  print_expression e Format.str_formatter;
  Format.flush_str_formatter ()

let string_of_computation c =
  print_computation c Format.str_formatter;
  Format.flush_str_formatter ()
