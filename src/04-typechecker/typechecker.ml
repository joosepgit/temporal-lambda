open Utils
module Ast = Language.Ast
module Const = Language.Const

type state = {
  variables :
    (Ast.ty_param list * Context.tau_param list * Ast.ty) Ast.VariableContext.t;
  type_definitions : (Ast.ty_param list * Ast.ty_def) Ast.TyNameMap.t;
}

let initial_state =
  {
    variables = Ast.VariableContext.empty;
    type_definitions =
      (Ast.TyNameMap.empty
      |> Ast.TyNameMap.add Ast.bool_ty_name
           ([], Ast.TyInline (Ast.TyConst Const.BooleanTy))
      |> Ast.TyNameMap.add Ast.int_ty_name
           ([], Ast.TyInline (Ast.TyConst Const.IntegerTy))
      |> Ast.TyNameMap.add Ast.unit_ty_name ([], Ast.TyInline (Ast.TyTuple []))
      |> Ast.TyNameMap.add Ast.string_ty_name
           ([], Ast.TyInline (Ast.TyConst Const.StringTy))
      |> Ast.TyNameMap.add Ast.float_ty_name
           ([], Ast.TyInline (Ast.TyConst Const.FloatTy))
      |> Ast.TyNameMap.add Ast.empty_ty_name ([], Ast.TySum [])
      |>
      let a = Ast.TyParam.fresh "list" in
      Ast.TyNameMap.add Ast.list_ty_name
        ( [ a ],
          Ast.TySum
            [
              (Ast.nil_label, None);
              ( Ast.cons_label,
                Some
                  (Ast.TyTuple
                     [
                       Ast.TyParam a;
                       Ast.TyApply (Ast.list_ty_name, [ Ast.TyParam a ]);
                     ]) );
            ] ));
  }

let rec check_ty state = function
  | Ast.TyConst _ -> ()
  | TyApply (ty_name, tys) ->
      let params, _ = Ast.TyNameMap.find ty_name state.type_definitions in
      let expected, actual = (List.length params, List.length tys) in
      if expected <> actual then
        Error.typing "Type %t expects %d arguments but got %d."
          (Ast.TyName.print ty_name) expected actual
      else List.iter (check_ty state) tys
  | TyParam _ -> ()
  | TyArrow (ty1, ty2) ->
      check_ty state ty1;
      check_comp_ty state ty2
  | TyTuple tys -> List.iter (check_ty state) tys
  | TyBox (_, ty) -> check_ty state ty

and check_comp_ty state = function Ast.CompTy (ty, _tau) -> check_ty state ty

let check_variant state (_label, arg_ty) =
  match arg_ty with None -> () | Some ty -> check_ty state ty

let check_ty_def state = function
  | Ast.TySum defs -> List.iter (check_variant state) defs
  | Ast.TyInline ty -> check_ty state ty

let fresh_ty () =
  let a = Ast.TyParam.fresh "ty" in
  Ast.TyParam a

let fresh_tau () =
  let t = Context.TauParamModule.fresh "tau" in
  Context.TauParam t

let fresh_comp_ty () = Ast.CompTy (fresh_ty (), fresh_tau ())

let extend_variables state vars =
  List.fold_left
    (fun state (x, ty) ->
      let updated_variables =
        Ast.VariableContext.add_variable x ([], [], ty) state.variables
      in
      { state with variables = updated_variables })
    state vars

let extend_temporal state t =
  let updated_variables = Ast.VariableContext.add_temp t state.variables in
  { state with variables = updated_variables }

let refreshing_ty_subst params =
  List.fold_left
    (fun subst param ->
      let ty = fresh_ty () in
      Ast.TyParamMap.add param ty subst)
    Ast.TyParamMap.empty params

let refreshing_tau_subst params =
  List.fold_left
    (fun subst param ->
      let tau = fresh_tau () in
      Context.TauParamMap.add param tau subst)
    Context.TauParamMap.empty params

let infer_variant state lbl =
  let rec find = function
    | [] -> assert false
    | (_, (_, Ast.TyInline _)) :: ty_defs -> find ty_defs
    | (ty_name, (params, Ast.TySum variants)) :: ty_defs -> (
        match List.assoc_opt lbl variants with
        | None -> find ty_defs
        | Some ty -> (ty_name, params, ty))
  in
  let ty_name, params, ty =
    find (Ast.TyNameMap.bindings state.type_definitions)
  in
  let ty_subst = refreshing_ty_subst params in
  let tau_subst = refreshing_tau_subst [] in
  let args = List.map (fun param -> Ast.TyParamMap.find param ty_subst) params
  and ty' = Option.map (Ast.substitute_ty ty_subst tau_subst) ty in
  (ty', Ast.TyApply (ty_name, args))

let rec infer_pattern state = function
  | Ast.PVar x ->
      let ty = fresh_ty () in
      (ty, [ (x, ty) ], [])
  | Ast.PAs (pat, x) ->
      let ty, vars, eqs = infer_pattern state pat in
      (ty, (x, ty) :: vars, eqs)
  | Ast.PAnnotated (pat, ty) ->
      let ty', vars, eqs = infer_pattern state pat in
      (ty, vars, Either.Left (ty, ty') :: eqs)
  | Ast.PConst c -> (Ast.TyConst (Const.infer_ty c), [], [])
  | Ast.PNonbinding ->
      let ty = fresh_ty () in
      (ty, [], [])
  | Ast.PTuple pats ->
      let fold pat (tys, vars, eqs) =
        let ty', vars', eqs' = infer_pattern state pat in
        (ty' :: tys, vars' @ vars, eqs' @ eqs)
      in
      let tys, vars, eqs = List.fold_right fold pats ([], [], []) in
      (Ast.TyTuple tys, vars, eqs)
  | Ast.PVariant (lbl, pat) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, pat) with
      | None, None -> (ty_out, [], [])
      | Some ty_in, Some pat ->
          let ty, vars, eqs = infer_pattern state pat in
          (ty_out, vars, Either.Left (ty_in, ty) :: eqs)
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch")

let rec infer_expression state = function
  | Ast.Var x ->
      let ty_params, tau_params, ty =
        Ast.VariableContext.find_variable x state.variables
      in
      let ty_subst = refreshing_ty_subst ty_params in
      let tau_subst = refreshing_tau_subst tau_params in
      (Ast.substitute_ty ty_subst tau_subst ty, [])
  | Ast.Const c -> (Ast.TyConst (Const.infer_ty c), [])
  | Ast.Annotated (expr, ty) ->
      let ty', eqs = infer_expression state expr in
      (ty, Either.Left (ty, ty') :: eqs)
  | Ast.Tuple exprs ->
      let fold expr (tys, eqs) =
        let ty', eqs' = infer_expression state expr in
        (ty' :: tys, eqs' @ eqs)
      in
      let tys, eqs = List.fold_right fold exprs ([], []) in
      (Ast.TyTuple tys, eqs)
  | Ast.Lambda abs ->
      let ty, ty', eqs = infer_abstraction state abs in
      (Ast.TyArrow (ty, ty'), eqs)
  | Ast.RecLambda (f, abs) ->
      let f_ty = fresh_ty () in
      let state' = extend_variables state [ (f, f_ty) ] in
      let ty, ty', eqs = infer_abstraction state' abs in
      let out_ty = Ast.TyArrow (ty, ty') in
      (out_ty, Either.Left (f_ty, out_ty) :: eqs)
  | Ast.Variant (lbl, expr) -> (
      let ty_in, ty_out = infer_variant state lbl in
      match (ty_in, expr) with
      | None, None -> (ty_out, [])
      | Some ty_in, Some expr ->
          let ty, eqs = infer_expression state expr in
          (ty_out, Either.Left (ty_in, ty) :: eqs)
      | None, Some _ | Some _, None ->
          Error.typing "Variant optional argument mismatch")

and infer_computation state = function
  | Ast.Return expr ->
      let ty, eqs = infer_expression state expr in
      (Ast.CompTy (ty, Context.TauConst 0), eqs)
  | Ast.Do (comp1, comp2) ->
      let CompTy (ty1, tau1), eqs1 = infer_computation state comp1 in
      let state' = extend_temporal state tau1 in
      let ty1', CompTy (ty2, tau2), eqs2 = infer_abstraction state' comp2 in
      ( CompTy (ty2, Context.TauAdd (tau1, tau2)),
        (Either.Left (ty1, ty1') :: eqs1) @ eqs2 )
  | Ast.Apply (e1, e2) ->
      let t1, eqs1 = infer_expression state e1
      and t2, eqs2 = infer_expression state e2
      and a = fresh_comp_ty () in
      (a, (Either.Left (t1, Ast.TyArrow (t2, a)) :: eqs1) @ eqs2)
  | Ast.Match (e, cases) ->
      let ty1, eqs = infer_expression state e
      and branch_comp_ty = fresh_comp_ty () in
      let (CompTy (branch_ty, branch_tau)) = branch_comp_ty in
      let fold eqs abs =
        let ty1', CompTy (branch_ty', branch_tau'), eqs' =
          infer_abstraction state abs
        in
        Either.Left (ty1, ty1')
        :: Either.Left (branch_ty, branch_ty')
        :: Either.Right (branch_tau, branch_tau')
        :: eqs'
        @ eqs
      in
      (branch_comp_ty, List.fold_left fold eqs cases)
  | Ast.Delay (tau, c) ->
      let state' = extend_temporal state tau in
      let CompTy (ty, tau'), eqs = infer_computation state' c in
      (CompTy (ty, Context.TauAdd (tau, tau')), eqs)
  | Ast.Box (tau, e, abs) ->
      let state_ahead = extend_temporal state tau in
      let value_ty, eqs = infer_expression state_ahead e in
      let value_ty', comp_ty, eqs' = infer_abstraction state abs in
      ( comp_ty,
        (Either.Left (Ast.TyBox (tau, value_ty), value_ty') :: eqs) @ eqs' )

and infer_abstraction state (pat, comp) =
  let ty, vars, eqs = infer_pattern state pat in
  let state' = extend_variables state vars in
  let ty', eqs' = infer_computation state' comp in
  (ty, ty', eqs @ eqs')

let subst_equations ty_subst tau_subst =
  let subst_equation = function
    | Either.Left (t1, t2) ->
        Either.Left
          ( Ast.substitute_ty ty_subst tau_subst t1,
            Ast.substitute_ty ty_subst tau_subst t2 )
    | Either.Right (tau1, tau2) ->
        Either.Right
          (Ast.substitute_tau tau_subst tau1, Ast.substitute_tau tau_subst tau2)
  in
  List.map subst_equation

let add_ty_subst a ty ty_subst tau_subst =
  Ast.TyParamMap.add a (Ast.substitute_ty ty_subst tau_subst ty) ty_subst

let add_tau_subst tp tau tau_subst =
  Context.TauParamMap.add tp (Ast.substitute_tau tau_subst tau) tau_subst

let rec occurs_ty a = function
  | Ast.TyParam a' -> a = a'
  | Ast.TyConst _ -> false
  | Ast.TyArrow (ty1, CompTy (ty2, _)) -> occurs_ty a ty1 || occurs_ty a ty2
  | Ast.TyApply (_, tys) -> List.exists (occurs_ty a) tys
  | Ast.TyTuple tys -> List.exists (occurs_ty a) tys
  | Ast.TyBox (_, ty) -> occurs_ty a ty

let rec occurs_tau a = function
  | Context.TauParam a' -> a = a'
  | Context.TauConst _ -> false
  | Context.TauAdd (tau, tau') -> occurs_tau a tau || occurs_tau a tau'

let is_transparent_type state ty_name =
  match Ast.TyNameMap.find ty_name state.type_definitions with
  | _, Ast.TySum _ -> false
  | _, Ast.TyInline _ -> true

let unfold state ty_name args =
  match Ast.TyNameMap.find ty_name state.type_definitions with
  | _, Ast.TySum _ -> assert false
  | params, Ast.TyInline ty ->
      let ty_subst =
        List.combine params args |> List.to_seq |> Ast.TyParamMap.of_seq
      in
      let tau_subst = refreshing_tau_subst [] in
      Ast.substitute_ty ty_subst tau_subst ty

let rec simplify_tau tau =
  match tau with
  | Context.TauAdd (t1, t2) -> (
      let t1' = simplify_tau t1 in
      let t2' = simplify_tau t2 in
      match (t1', t2') with
      | Context.TauConst c1, Context.TauConst c2 -> Context.TauConst (c1 + c2)
      | Context.TauConst 0, t | t, Context.TauConst 0 -> t
      | _ -> Context.TauAdd (t1', t2'))
  | _ -> tau

and simplify_ty ty =
  match ty with
  | Ast.TyConst t -> Ast.TyConst t
  | TyApply (ty_name, ty_list) -> TyApply (ty_name, List.map simplify_ty ty_list)
  | TyParam ty_param -> TyParam ty_param
  | TyArrow (ty, Ast.CompTy (ty', tau')) ->
      TyArrow (simplify_ty ty, Ast.CompTy (simplify_ty ty', simplify_tau tau'))
  | TyTuple ty_list -> TyTuple (List.map simplify_ty ty_list)
  | TyBox (tau, ty) -> TyBox (simplify_tau tau, simplify_ty ty)

let simplify_comp_ty = function
  | Ast.CompTy (ty, tau) -> Ast.CompTy (simplify_ty ty, simplify_tau tau)

let rec unify state = function
  | [] -> (Ast.TyParamMap.empty, Context.TauParamMap.empty)
  | Either.Left (t1, t2) :: eqs when t1 = t2 -> unify state eqs
  | Either.Right (tau1, tau2) :: eqs -> (
      let tau1' = simplify_tau tau1 in
      let tau2' = simplify_tau tau2 in
      match (tau1', tau2') with
      | Context.TauParam p1, Context.TauParam p2 when p1 = p2 -> unify state eqs
      | Context.TauParam tp, tau when not (occurs_tau tp tau) ->
          let ty_subst, tau_subst =
            unify state
              (subst_equations Ast.TyParamMap.empty
                 (Context.TauParamMap.singleton tp tau)
                 eqs)
          in
          (ty_subst, add_tau_subst tp tau tau_subst)
      | tau, Context.TauParam tp when not (occurs_tau tp tau) ->
          let ty_subst, tau_subst =
            unify state
              (subst_equations Ast.TyParamMap.empty
                 (Context.TauParamMap.singleton tp tau)
                 eqs)
          in
          (ty_subst, add_tau_subst tp tau tau_subst)
      | Context.TauConst 0, Context.TauAdd (t1, t2)
      | Context.TauAdd (t1, t2), Context.TauConst 0 ->
          unify state
            (Either.Right (t1, Context.TauConst 0)
            :: Either.Right (t2, Context.TauConst 0)
            :: eqs)
      | _ when tau1' = tau2' ->
          unify state eqs (* Compare simplified versions *)
      | _ ->
          let print_param = Ast.TauPrintParam.create () in
          Error.typing "Cannot unify temporal values %t = %t"
            (fun ppf -> Ast.VariableContext.print_tau print_param tau1 ppf)
            (fun ppf -> Ast.VariableContext.print_tau print_param tau2 ppf))
  | Either.Left (Ast.TyApply (ty_name1, args1), Ast.TyApply (ty_name2, args2))
    :: eqs
    when ty_name1 = ty_name2 ->
      let new_eqs =
        List.map
          (fun (t1, t2) -> Either.Left (t1, t2))
          (List.combine args1 args2)
      in
      unify state (new_eqs @ eqs)
  | Either.Left (Ast.TyApply (ty_name, args), ty) :: eqs
    when is_transparent_type state ty_name ->
      unify state (Either.Left (unfold state ty_name args, ty) :: eqs)
  | Either.Left (ty, Ast.TyApply (ty_name, args)) :: eqs
    when is_transparent_type state ty_name ->
      unify state (Either.Left (ty, unfold state ty_name args) :: eqs)
  | Either.Left (Ast.TyTuple tys1, Ast.TyTuple tys2) :: eqs
    when List.length tys1 = List.length tys2 ->
      let new_eqs =
        List.map (fun (t1, t2) -> Either.Left (t1, t2)) (List.combine tys1 tys2)
      in
      unify state (new_eqs @ eqs)
  | Either.Left
      ( Ast.TyArrow (t1, CompTy (t1', tau1')),
        Ast.TyArrow (t2, CompTy (t2', tau2')) )
    :: eqs ->
      unify state
        (Either.Left (t1, t2)
        :: Either.Left (t1', t2')
        :: Either.Right (tau1', tau2')
        :: eqs)
  | Either.Left (Ast.TyParam a, t) :: eqs when not (occurs_ty a t) ->
      let ty_subst, tau_subst =
        unify state
          (subst_equations
             (Ast.TyParamMap.singleton a t)
             Context.TauParamMap.empty eqs)
      in
      (add_ty_subst a t ty_subst tau_subst, tau_subst)
  | Either.Left (t, Ast.TyParam a) :: eqs when not (occurs_ty a t) ->
      let ty_subst, tau_subst =
        unify state
          (subst_equations
             (Ast.TyParamMap.singleton a t)
             Context.TauParamMap.empty eqs)
      in
      (add_ty_subst a t ty_subst tau_subst, tau_subst)
  | Either.Left (t1, t2) :: _ ->
      let ty_pp = Ast.TyPrintParam.create () in
      let tau_pp = Ast.TauPrintParam.create () in
      Error.typing "Cannot unify types %t = %t"
        (Ast.print_ty ty_pp tau_pp t1)
        (Ast.print_ty ty_pp tau_pp t2)

let infer state e =
  let comp_ty, eqs = infer_computation state e in
  let ty_subst, tau_subst = unify state eqs in
  let comp_ty' = Ast.substitute_comp_ty ty_subst tau_subst comp_ty in
  simplify_comp_ty comp_ty'

let add_external_function x ty_sch state =
  {
    state with
    variables = Ast.VariableContext.add_variable x ty_sch state.variables;
  }

let add_top_definition state x expr =
  let ty, eqs = infer_expression state expr in
  let ty_subst, tau_subst = unify state eqs in
  let ty' = Ast.substitute_ty ty_subst tau_subst ty in
  let ty'' = simplify_ty ty' in
  let free_vars = Ast.free_vars ty'' |> Ast.TyParamSet.elements in
  let ty_sch = (free_vars, [], ty'') in
  add_external_function x ty_sch state

let add_type_definitions state ty_defs =
  let state' =
    List.fold_left
      (fun state (params, ty_name, ty_def) ->
        {
          state with
          type_definitions =
            Ast.TyNameMap.add ty_name (params, ty_def) state.type_definitions;
        })
      state ty_defs
  in
  List.iter (fun (_, _, ty_def) -> check_ty_def state' ty_def) ty_defs;
  state'

let load_primitive state x prim =
  let ty_sch = Primitives.primitive_type_scheme prim in
  add_external_function x ty_sch state
