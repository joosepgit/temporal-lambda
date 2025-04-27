open Utils
module Variable = Symbol.Make ()
module VariableMap = Map.Make (Variable)
module VariableContext = Context.Make (Variable) (Map.Make (Variable))
module Label = Symbol.Make ()
module TyName = Symbol.Make ()

type ty_name = TyName.t

module TyNameMap = Map.Make (TyName)

let bool_ty_name = TyName.fresh "bool"
let int_ty_name = TyName.fresh "int"
let unit_ty_name = TyName.fresh "unit"
let string_ty_name = TyName.fresh "string"
let float_ty_name = TyName.fresh "float"
let list_ty_name = TyName.fresh "list"
let empty_ty_name = TyName.fresh "empty"

type ty =
  | TyConst of Const.ty
  | TyApply of ty_name * ty list  (** [(ty1, ty2, ..., tyn) type_name] *)
  | TyParam of Context.ty_param  (** ['a] *)
  | TyArrow of ty * comp_ty  (** [ty1 -> ty2 ! tau] *)
  | TyTuple of ty list  (** [ty1 * ty2 * ... * tyn] *)
  | TyBox of Context.tau * ty  (** [ [tau]ty ] *)

and comp_ty = CompTy of ty * Context.tau  (** [ty ! tau] *)

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
        (Context.print_tau tau_print_param tau)
  | TyTuple [] -> print "unit"
  | TyTuple tys ->
      print ~at_level:2 "%t"
        (Print.print_sequence " × "
           (print_ty ~max_level:1 ty_print_param tau_print_param)
           tys)
  | TyBox (tau, ty) ->
      print ~at_level:1 "[%t]%t"
        (Context.print_tau tau_print_param tau)
        (print_ty ~max_level:0 ty_print_param tau_print_param ty)

let print_ty_params ?max_level ty_pp ty_params ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  Format.fprintf ppf "[";
  let rec print_helper = function
    | [] -> ()
    | [ last ] -> print "%t" (ty_pp last)
    | hd :: tl ->
        print "%t" (ty_pp hd);
        Format.fprintf ppf ", ";
        print_helper tl
  in
  print_helper ty_params;
  Format.fprintf ppf "]"

let print_tau_params ?max_level tau_pp tau_params ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  Format.fprintf ppf "[";
  let rec print_helper = function
    | [] -> ()
    | [ last ] -> print "%t" (tau_pp last)
    | hd :: tl ->
        print "%t" (tau_pp hd);
        Format.fprintf ppf ", ";
        print_helper tl
  in
  print_helper tau_params;
  Format.fprintf ppf "]"

let rec substitute_tau subst = function
  | Context.TauConst _ as tau -> tau
  | Context.TauParam tp as tau -> (
      match Context.TauParamMap.find_opt tp subst with
      | None -> tau
      | Some tau' -> tau')
  | Context.TauAdd (tau, tau') ->
      Context.TauAdd (substitute_tau subst tau, substitute_tau subst tau')

let rec substitute_ty ty_subst tau_subst = function
  | TyConst _ as ty -> ty
  | TyParam a as ty -> (
      match Context.TyParamMap.find_opt a ty_subst with
      | None -> ty
      | Some ty' -> ty')
  | TyApply (ty_name, tys) ->
      TyApply (ty_name, List.map (substitute_ty ty_subst tau_subst) tys)
  | TyTuple tys -> TyTuple (List.map (substitute_ty ty_subst tau_subst) tys)
  | TyArrow (ty1, CompTy (ty2, tau)) ->
      TyArrow
        ( substitute_ty ty_subst tau_subst ty1,
          CompTy
            (substitute_ty ty_subst tau_subst ty2, substitute_tau tau_subst tau)
        )
  | TyBox (tau, ty) ->
      TyBox (substitute_tau tau_subst tau, substitute_ty ty_subst tau_subst ty)

let substitute_comp_ty ty_subst tau_subst = function
  | CompTy (ty, tau) ->
      CompTy (substitute_ty ty_subst tau_subst ty, substitute_tau tau_subst tau)

let rec free_vars = function
  | TyConst _ -> (Context.TyParamSet.empty, Context.TauParamSet.empty)
  | TyParam a -> (Context.TyParamSet.singleton a, Context.TauParamSet.empty)
  | TyApply (_, tys) ->
      List.fold_left
        (fun (ty_params, tau_params) ty ->
          let fv_ty, fv_tau = free_vars ty in
          ( Context.TyParamSet.union ty_params fv_ty,
            Context.TauParamSet.union tau_params fv_tau ))
        (Context.TyParamSet.empty, Context.TauParamSet.empty)
        tys
  | TyTuple tys ->
      List.fold_left
        (fun (ty_params, tau_params) ty ->
          let fv_ty, fv_tau = free_vars ty in
          ( Context.TyParamSet.union ty_params fv_ty,
            Context.TauParamSet.union tau_params fv_tau ))
        (Context.TyParamSet.empty, Context.TauParamSet.empty)
        tys
  | TyArrow (ty1, CompTy (ty2, tau)) ->
      let fv_ty1, fv_tau1 = free_vars ty1 in
      let fv_ty2, fv_tau2 = free_vars ty2 in
      let nested_free_taus = free_taus tau in
      ( Context.TyParamSet.union fv_ty1 fv_ty2,
        Context.TauParamSet.union
          (Context.TauParamSet.union fv_tau1 fv_tau2)
          nested_free_taus )
  | TyBox (tau, ty) ->
      let fv_ty, fv_tau = free_vars ty in
      let nested_free_taus = free_taus tau in
      (fv_ty, Context.TauParamSet.union fv_tau nested_free_taus)

and free_taus tau =
  match tau with
  | Context.TauConst _ -> Context.TauParamSet.empty
  | Context.TauParam a -> Context.TauParamSet.singleton a
  | Context.TauAdd (l, r) ->
      Context.TauParamSet.union (free_taus l) (free_taus r)

type variable = Variable.t
type label = Label.t

let nil_label_string = "$nil$"
let nil_label = Label.fresh nil_label_string
let cons_label_string = "$cons$"
let cons_label = Label.fresh cons_label_string

type pattern =
  | PVar of variable
  | PAnnotated of pattern * ty
  | PAs of pattern * variable
  | PTuple of pattern list
  | PVariant of label * pattern option
  | PConst of Const.t
  | PNonbinding

type expression =
  | Var of variable
  | Const of Const.t
  | Annotated of expression * ty
  | Tuple of expression list
  | Variant of label * expression option
  | Lambda of abstraction
  | RecLambda of variable * abstraction

and computation =
  | Return of expression
  | Do of computation * abstraction
  | Match of expression * abstraction list
  | Apply of expression * expression
  | Delay of Context.tau * computation
  | Box of Context.tau * expression * abstraction
  | Unbox of Context.tau * expression * abstraction

and abstraction = pattern * computation

type ty_def = TySum of (label * ty option) list | TyInline of ty

type command =
  | TyDef of (Context.ty_param list * ty_name * ty_def) list
  | TopLet of variable * expression
  | TopDo of computation

type evaluation_environment = {
  state : expression VariableContext.t;
  variables : expression VariableContext.t;
  builtin_functions : (expression -> computation) VariableContext.t;
}

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
      let print_param = Context.TauPrintParam.create () in
      print ~at_level:1 "delay %t %t"
        (Context.print_tau print_param tau)
        (print_computation c)
  | Box (tau, e, (p, c)) ->
      let print_param = Context.TauPrintParam.create () in
      print ~at_level:1 "box %t[%t] as %t in %t"
        (Context.print_tau print_param tau)
        (print_expression e) (print_pattern p) (print_computation c)
  | Unbox (tau, e, (p, c)) ->
      let print_param = Context.TauPrintParam.create () in
      print ~at_level:1 "unbox %t[%t] as %t in %t"
        (Context.print_tau print_param tau)
        (print_expression e) (print_pattern p) (print_computation c)

and print_abstraction (p, c) ppf =
  Format.fprintf ppf "%t ↦ %t" (print_pattern p) (print_computation c)

and print_case a ppf = Format.fprintf ppf "%t" (print_abstraction a)

let string_of_expression e =
  print_expression e Format.str_formatter;
  Format.flush_str_formatter ()

let string_of_computation c =
  print_computation c Format.str_formatter;
  Format.flush_str_formatter ()

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
  VariableContext.print_vars_and_tys print_var_and_ty ctx

let print_interpreter_state ctx =
  let print_var_and_expr (variable, expr) ppf =
    Variable.print variable ppf;
    Format.fprintf ppf " -> ";
    print_expression expr ppf
  in
  let ppf = Format.str_formatter in
  VariableContext.print_vars_and_exprs print_var_and_expr ctx ppf;
  Format.flush_str_formatter ()
