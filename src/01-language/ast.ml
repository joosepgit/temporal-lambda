module Symbol = Utils.Symbol
module Variable = Symbol.Make ()
module VariableMap = Map.Make (Variable)
module Label = Symbol.Make ()
module TyName = Symbol.Make ()

type ty_name = TyName.t

module TyNameMap = Map.Make (TyName)
module TyParamModule = Symbol.Make ()
module TyParamMap = Map.Make (TyParamModule)
module TyParamSet = Set.Make (TyParamModule)

type ty_param = TyParamModule.t

module TauParamModule = Symbol.Make ()
module TauParamMap = Map.Make (TauParamModule)
module TauParamSet = Set.Make (TauParamModule)

type tau_param = TauParamModule.t
type tau = TauConst of int | TauParam of tau_param | TauAdd of tau * tau

type ty =
  | TyConst of Const.ty
  | TyApply of ty_name * ty list  (** [(ty1, ty2, ..., tyn) type_name] *)
  | TyParam of ty_param  (** ['a] *)
  | TyArrow of ty * comp_ty  (** [ty1 -> ty2 ! tau] *)
  | TyTuple of ty list  (** [ty1 * ty2 * ... * tyn] *)
  | TyBox of tau * ty  (** [ [tau]ty ] *)

and comp_ty = CompTy of ty * tau  (** [ty ! tau] *)

let bool_ty_name = TyName.fresh "bool"
let int_ty_name = TyName.fresh "int"
let unit_ty_name = TyName.fresh "unit"
let string_ty_name = TyName.fresh "string"
let float_ty_name = TyName.fresh "float"
let list_ty_name = TyName.fresh "list"
let empty_ty_name = TyName.fresh "empty"

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
  | PureLambda of abstraction
  | RecLambda of variable * abstraction

and computation =
  | Return of expression
  | Do of computation * abstraction
  | Match of expression * abstraction list
  | Apply of expression * expression
  | Delay of tau * computation
  | Box of tau * expression * abstraction
  | Unbox of tau * expression * abstraction

and abstraction = pattern * computation

type ty_def = TySum of (label * ty option) list | TyInline of ty

type command =
  | TyDef of (ty_param list * ty_name * ty_def) list
  | TopLet of variable * expression
  | TopDo of computation

type ('var, 'map, 'value) context_elem_ty = VarMap of 'map | Tau of tau
type ('var, 'map, 'value) context = ('var, 'map, 'value) context_elem_ty list

let rec substitute_tau subst = function
  | TauConst _ as tau -> tau
  | TauParam tp as tau -> (
      match TauParamMap.find_opt tp subst with None -> tau | Some tau' -> tau')
  | TauAdd (tau, tau') ->
      TauAdd (substitute_tau subst tau, substitute_tau subst tau')

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
  | TyConst _ -> (TyParamSet.empty, TauParamSet.empty)
  | TyParam a -> (TyParamSet.singleton a, TauParamSet.empty)
  | TyApply (_, tys) ->
      List.fold_left
        (fun (ty_params, tau_params) ty ->
          let fv_ty, fv_tau = free_vars ty in
          (TyParamSet.union ty_params fv_ty, TauParamSet.union tau_params fv_tau))
        (TyParamSet.empty, TauParamSet.empty)
        tys
  | TyTuple tys ->
      List.fold_left
        (fun (ty_params, tau_params) ty ->
          let fv_ty, fv_tau = free_vars ty in
          (TyParamSet.union ty_params fv_ty, TauParamSet.union tau_params fv_tau))
        (TyParamSet.empty, TauParamSet.empty)
        tys
  | TyArrow (ty1, CompTy (ty2, tau)) ->
      let fv_ty1, fv_tau1 = free_vars ty1 in
      let fv_ty2, fv_tau2 = free_vars ty2 in
      let nested_free_taus = free_taus tau in
      ( TyParamSet.union fv_ty1 fv_ty2,
        TauParamSet.union (TauParamSet.union fv_tau1 fv_tau2) nested_free_taus
      )
  | TyBox (tau, ty) ->
      let fv_ty, fv_tau = free_vars ty in
      let nested_free_taus = free_taus tau in
      (fv_ty, TauParamSet.union fv_tau nested_free_taus)

and free_taus tau =
  match tau with
  | TauConst _ -> TauParamSet.empty
  | TauParam a -> TauParamSet.singleton a
  | TauAdd (l, r) -> TauParamSet.union (free_taus l) (free_taus r)
