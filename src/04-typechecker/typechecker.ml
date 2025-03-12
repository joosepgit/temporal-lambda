open Utils
module Ast = Language.Ast
module Const = Language.Const

type state = {
  variables : (Ast.ty_param list * Ast.ty) Ast.VariableContext.t;
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

and check_comp_ty state = function Ast.CompTy (ty, _tau) -> check_ty state ty

let check_variant state (_label, arg_ty) =
  match arg_ty with None -> () | Some ty -> check_ty state ty

let check_ty_def state = function
  | Ast.TySum defs -> List.iter (check_variant state) defs
  | Ast.TyInline ty -> check_ty state ty

let fresh_ty () =
  let a = Ast.TyParam.fresh "ty" in
  Ast.TyParam a

and fresh_comp_ty () =
  let a = Ast.TyParam.fresh "ty" in
  let t = Context.TauParamModule.fresh "tau" in
  Ast.CompTy (Ast.TyParam a, Ast.VariableContext.TauParam t)

let extend_variables state vars =
  List.fold_left
    (fun state (x, ty) ->
      let updated_variables =
        Ast.VariableContext.add_variable x ([], ty) state.variables
      in
      { state with variables = updated_variables })
    state vars

let extend_temporal state t =
  let updated_variables = Ast.VariableContext.add_temp t state.variables in
  { state with variables = updated_variables }

let refreshing_subst params =
  List.fold_left
    (fun subst param ->
      let ty = fresh_ty () in
      Ast.TyParamMap.add param ty subst)
    Ast.TyParamMap.empty params

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
  let subst = refreshing_subst params in
  let args = List.map (fun param -> Ast.TyParamMap.find param subst) params
  and ty' = Option.map (Ast.substitute_ty subst) ty in
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
      let params, ty = Ast.VariableContext.find_variable x state.variables in
      let subst = refreshing_subst params in
      (Ast.substitute_ty subst ty, [])
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
      (Ast.CompTy (ty, Ast.VariableContext.TauConst 0), eqs)
  | Ast.Do (comp1, comp2) ->
      let CompTy (ty1, tau1), eqs1 = infer_computation state comp1 in
      let state' = extend_temporal state tau1 in
      let ty1', CompTy (ty2, tau2), eqs2 = infer_abstraction state' comp2 in
      ( CompTy (ty2, Ast.VariableContext.TauAdd (tau1, tau2)),
        (Either.Left (ty1, ty1') :: Either.Right (tau1, tau2) :: eqs1) @ eqs2 )
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
  | Ast.Delay (tau, comp) ->
      let state' = extend_temporal state tau in
      let CompTy (ty, tau'), eqs = infer_computation state' comp in
      (CompTy (ty, Ast.VariableContext.TauAdd (tau, tau')), eqs)

and infer_abstraction state (pat, comp) =
  let ty, vars, eqs = infer_pattern state pat in
  let state' = extend_variables state vars in
  let ty', eqs' = infer_computation state' comp in
  (ty, ty', eqs @ eqs')

let subst_equations sbst =
  let subst_equation = function
    | Either.Left (t1, t2) ->
        Either.Left (Ast.substitute_ty sbst t1, Ast.substitute_ty sbst t2)
    | Either.Right (tau1, tau2) -> Either.Right (tau1, tau2)
  in
  List.map subst_equation

let add_subst a t sbst = Ast.TyParamMap.add a (Ast.substitute_ty sbst t) sbst

let rec occurs a = function
  | Ast.TyParam a' -> a = a'
  | Ast.TyConst _ -> false
  | Ast.TyArrow (ty1, CompTy (ty2, _tau)) -> occurs a ty1 || occurs a ty2
  | Ast.TyApply (_, tys) -> List.exists (occurs a) tys
  | Ast.TyTuple tys -> List.exists (occurs a) tys

let is_transparent_type state ty_name =
  match Ast.TyNameMap.find ty_name state.type_definitions with
  | _, Ast.TySum _ -> false
  | _, Ast.TyInline _ -> true

let unfold state ty_name args =
  match Ast.TyNameMap.find ty_name state.type_definitions with
  | _, Ast.TySum _ -> assert false
  | params, Ast.TyInline ty ->
      let subst =
        List.combine params args |> List.to_seq |> Ast.TyParamMap.of_seq
      in
      Ast.substitute_ty subst ty

let rec simplify_tau tau =
  match tau with
  | Ast.VariableContext.TauAdd
      (Ast.VariableContext.TauConst c1, Ast.VariableContext.TauConst c2) ->
      Ast.VariableContext.TauConst (c1 + c2)
  | Ast.VariableContext.TauAdd (Ast.VariableContext.TauConst 0, t)
  | Ast.VariableContext.TauAdd (t, Ast.VariableContext.TauConst 0) ->
      simplify_tau t
  | Ast.VariableContext.TauAdd (t1, t2) -> (
      let t1' = simplify_tau t1 in
      let t2' = simplify_tau t2 in
      match (t1', t2') with
      | Ast.VariableContext.TauConst c1, Ast.VariableContext.TauConst c2 ->
          Ast.VariableContext.TauConst (c1 + c2)
      | Ast.VariableContext.TauConst 0, t | t, Ast.VariableContext.TauConst 0 ->
          t
      | _ -> Ast.VariableContext.TauAdd (t1', t2')
      (* Keep symbolic form *))
  | _ -> tau (* Keep symbolic values like TauParam unchanged *)

let rec unify state = function
  | [] -> Ast.TyParamMap.empty
  | Either.Left (t1, t2) :: eqs when t1 = t2 -> unify state eqs
  | Either.Right (tau1, tau2) :: eqs -> (
      let tau1' = simplify_tau tau1 in
      let tau2' = simplify_tau tau2 in
      match (tau1', tau2') with
      | Ast.VariableContext.TauParam p1, Ast.VariableContext.TauParam p2
        when p1 = p2 ->
          unify state eqs
      | Ast.VariableContext.TauParam p, t | t, Ast.VariableContext.TauParam p ->
          (* Substitution or constraint? *)
          let print_param = Ast.new_print_param () in
          Error.typing "Cannot unify temporal values %t = %t"
            (fun ppf ->
              Ast.VariableContext.print_tau print_param
                (Ast.VariableContext.TauParam p) ppf)
            (fun ppf -> Ast.VariableContext.print_tau print_param t ppf)
      | _ when tau1' = tau2' ->
          unify state eqs (* Compare simplified versions *)
      | _ ->
          let print_param = Ast.new_print_param () in
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
      ( Ast.TyArrow (t1, CompTy (t1', _tau1')),
        Ast.TyArrow (t2, CompTy (t2', _tau2')) )
    :: eqs ->
      unify state (Either.Left (t1, t2) :: Either.Left (t1', t2') :: eqs)
  | Either.Left (Ast.TyParam a, t) :: eqs when not (occurs a t) ->
      add_subst a t
        (unify state (subst_equations (Ast.TyParamMap.singleton a t) eqs))
  | Either.Left (t, Ast.TyParam a) :: eqs when not (occurs a t) ->
      add_subst a t
        (unify state (subst_equations (Ast.TyParamMap.singleton a t) eqs))
  | Either.Left (t1, t2) :: _ ->
      let print_param = Ast.new_print_param () in
      Error.typing "Cannot unify types %t = %t"
        (Ast.print_ty print_param t1)
        (Ast.print_ty print_param t2)

let infer state e =
  let CompTy (t, tau), eqs = infer_computation state e in
  let state' = extend_temporal state tau in
  let sbst = unify state' eqs in
  let t' = Ast.substitute_ty sbst t in
  t'

let add_external_function x ty_sch state =
  {
    state with
    variables = Ast.VariableContext.add_variable x ty_sch state.variables;
  }

let add_top_definition state x expr =
  let ty, eqs = infer_expression state expr in
  let subst = unify state eqs in
  let ty' = Ast.substitute_ty subst ty in
  let free_vars = Ast.free_vars ty' |> Ast.TyParamSet.elements in
  let ty_sch = (free_vars, ty') in
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
