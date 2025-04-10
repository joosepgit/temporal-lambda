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

module TyParam = Symbol.Make ()

type ty_param = TyParam.t

module TyParamMap = Map.Make (TyParam)
module TyParamSet = Set.Make (TyParam)
module TyPrintParam = Print.TyPrintParam (TyParamMap)
module TauPrintParam = Print.TauPrintParam (Context.TauParamMap)

type ty =
  | TyConst of Const.ty
  | TyApply of ty_name * ty list  (** [(ty1, ty2, ..., tyn) type_name] *)
  | TyParam of ty_param  (** ['a] *)
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
        (VariableContext.print_tau tau_print_param tau)
  | TyTuple [] -> print "unit"
  | TyTuple tys ->
      print ~at_level:2 "%t"
        (Print.print_sequence " × "
           (print_ty ~max_level:1 ty_print_param tau_print_param)
           tys)
  | TyBox (tau, ty) ->
      print ~at_level:1 "[%t]%t"
        (VariableContext.print_tau tau_print_param tau)
        (print_ty ~max_level:0 ty_print_param tau_print_param ty)

let print_ty_params ty_params ppf =
  Format.fprintf ppf "[";
  let rec print_helper = function
    | [] -> ()
    | [ last ] -> TyParam.print last ppf
    | hd :: tl ->
        TyParam.print hd ppf;
        Format.fprintf ppf ", ";
        print_helper tl
  in
  print_helper ty_params;
  Format.fprintf ppf "]"

let print_tau_params tau_params ppf =
  Format.fprintf ppf "[";
  let rec print_helper = function
    | [] -> ()
    | [ last ] -> Context.TauParamModule.print last ppf
    | hd :: tl ->
        Context.TauParamModule.print hd ppf;
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
      match TyParamMap.find_opt a ty_subst with None -> ty | Some ty' -> ty')
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
  | TyConst _ -> TyParamSet.empty
  | TyParam a -> TyParamSet.singleton a
  | TyApply (_, tys) ->
      List.fold_left
        (fun vars ty -> TyParamSet.union vars (free_vars ty))
        TyParamSet.empty tys
  | TyTuple tys ->
      List.fold_left
        (fun vars ty -> TyParamSet.union vars (free_vars ty))
        TyParamSet.empty tys
  | TyArrow (ty1, CompTy (ty2, _)) ->
      TyParamSet.union (free_vars ty1) (free_vars ty2)
  | TyBox (_, ty) -> free_vars ty

let print_var_and_ty ty_pp tau_pp (variable, (ty_params, tau_params, ty)) ppf =
  Variable.print variable ppf;
  Format.fprintf ppf " -> ";
  print_ty_params ty_params ppf;
  Format.fprintf ppf ", ";
  print_tau_params tau_params ppf;
  Format.fprintf ppf " ";
  Format.fprintf ppf "@[%t@]" (print_ty ty_pp tau_pp ty);
  Format.pp_print_flush ppf ()

let print_variable_context ctx =
  let ty_pp = TyPrintParam.create () in
  let tau_pp = TauPrintParam.create () in
  VariableContext.print_contents ty_pp tau_pp print_var_and_ty ctx

let add_dummy_nat_to_ctx nat ctx = VariableContext.add_temp nat ctx

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

and abstraction = pattern * computation

type ty_def = TySum of (label * ty option) list | TyInline of ty

type command =
  | TyDef of (ty_param list * ty_name * ty_def) list
  | TopLet of variable * expression
  | TopDo of computation

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
      let print_param = TauPrintParam.create () in
      print ~at_level:1 "delay %t %t"
        (VariableContext.print_tau print_param tau)
        (print_computation c)
  | Box (tau, e, (p, c)) ->
      let print_param = TauPrintParam.create () in
      print ~at_level:1 "box %t[%t] as %t in %t"
        (VariableContext.print_tau print_param tau)
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
