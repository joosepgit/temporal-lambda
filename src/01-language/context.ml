open Ast
open Exception
module Error = Utils.Error
module Symbol = Utils.Symbol

module type S = sig
  type var
  type base
  type 'a map_or_tau
  type 'a t

  val empty : 'a t
  val add_temp : base tau -> 'a t -> 'a t
  val add_variable : var -> 'a -> 'a t -> 'a t
  val find_variable : var -> 'a t -> 'a
  val find_variable_opt : var -> 'a t -> 'a option
  val abstract_tau_sum : 'a t -> base tau
  val eval_tau : base tau -> base
  val subtract_tau : base tau -> 'a t -> 'a t
end

module Make
    (Variable : Symbol.S)
    (VariableMap : Map.S with type key = Variable.t)
    (Base : Tau.S) =
struct
  type var = Variable.t
  type base = Base.t
  type base_tau = base tau
  type 'a map_or_tau = (var, 'a VariableMap.t, base_tau) context_elem_ty
  type 'a t = (var, 'a VariableMap.t, base_tau) context

  let empty : 'a t = []

  let add_temp (n : base_tau) (lst : 'a t) : 'a t =
    match n with TauConst z when z = Base.zero -> lst | _ -> Tau n :: lst

  let add_variable (key : var) (value : 'a) (lst : 'a t) : 'a t =
    match lst with
    | VarMap map :: rest ->
        let updated_map = VariableMap.add key value map in
        VarMap updated_map :: rest
    | _ ->
        let new_map = VariableMap.add key value VariableMap.empty in
        VarMap new_map :: lst

  let find_variable (key : var) (lst : 'a t) : 'a =
    let rec find = function
      | [] ->
          Variable.print key Format.str_formatter;
          raise (VariableNotFound (Format.flush_str_formatter ()))
      | VarMap map :: rest -> (
          match VariableMap.find_opt key map with
          | Some v -> v
          | None -> find rest)
      | Tau _ :: rest -> find rest
    in
    find lst

  let find_variable_opt (key : var) (lst : 'a t) : 'a option =
    let rec find = function
      | [] -> None
      | VarMap map :: rest -> (
          match VariableMap.find_opt key map with
          | Some v -> Some v
          | None -> find rest)
      | Tau _ :: rest -> find rest
    in
    find lst

  let sum_taus_added_after (key : var) (lst : 'a t) : base_tau =
    let rec go acc = function
      | [] ->
          Variable.print key Format.str_formatter;
          raise (VariableNotFound (Format.flush_str_formatter ()))
      | Tau t :: rest -> go (Ast.TauAdd (acc, t)) rest
      | VarMap map :: rest -> (
          match VariableMap.find_opt key map with
          | Some _ -> acc
          | None -> go acc rest)
    in
    go (Ast.TauConst Base.zero) lst

  let abstract_tau_sum (lst : 'a t) : base_tau =
    let rec sum acc = function
      | [] -> acc
      | Tau t :: rest -> sum (TauAdd (acc, t)) rest
      | VarMap _ :: rest -> sum acc rest
    in
    sum (TauConst Base.zero) lst

  let rec eval_tau (t : base_tau) : base =
    match t with
    | TauConst c -> c
    | TauParam _ ->
        raise (UnknownValueInEval "TauParam not supported in eval_tau")
    | TauAdd (t1, t2) -> Base.add (eval_tau t1) (eval_tau t2)

  let subtract_tau (tau : base_tau) (lst : 'a t) : 'a t =
    let rec subtract_eval_tau (t : base_tau) : base =
      match t with
      | TauConst c -> c
      | TauParam _ -> Base.zero (* Ignore unknown values *)
      | TauAdd (t1, t2) ->
          Base.add (subtract_eval_tau t1) (subtract_eval_tau t2)
    in
    let rec subtract remaining target =
      match (remaining, target) with
      | rem, tgt_val when tgt_val = Base.zero -> rem
      | [], _ -> Error.typing "Not enough tau to subtract"
      | VarMap _ :: rest, _ -> subtract rest target
      | Tau t :: rest, tgt_val ->
          let t_val = subtract_eval_tau t in
          if Base.greater tgt_val t_val then
            subtract rest (Base.subtract tgt_val t_val)
          else
            let remaining_tau = TauConst (Base.subtract t_val tgt_val) in
            Tau remaining_tau :: rest
    in
    subtract lst (subtract_eval_tau tau)
end
