open Ast
open Exception
module Error = Utils.Error
module Symbol = Utils.Symbol

module type S = sig
  type var
  type 'a map_or_tau
  type 'a t

  val empty : 'a t
  val add_temp : tau -> 'a t -> 'a t
  val add_variable : var -> 'a -> 'a t -> 'a t
  val find_variable : var -> 'a t -> 'a
  val find_variable_opt : var -> 'a t -> 'a option
  val abstract_tau_sum : 'a t -> tau
  val subtract_tau : tau -> 'a t -> 'a t
end

module Make
    (Variable : Symbol.S)
    (VariableMap : Map.S with type key = Variable.t) =
struct
  type var = Variable.t
  type 'a map_or_tau = (var, 'a VariableMap.t, 'a) context_elem_ty
  type 'a t = (var, 'a VariableMap.t, 'a) context

  let empty : 'a t = []

  let add_temp (n : tau) (lst : 'a t) : 'a t =
    if n = TauConst 0 then lst else Tau n :: lst

  let add_variable (key : Variable.t) (value : 'a) (lst : 'a t) : 'a t =
    match lst with
    | VarMap map :: rest ->
        let updated_map = VariableMap.add key value map in
        VarMap updated_map :: rest
    | _ ->
        let new_map = VariableMap.add key value VariableMap.empty in
        VarMap new_map :: lst

  let find_variable (key : Variable.t) (lst : 'a t) : 'a =
    let rec find_in_maps maps =
      match maps with
      | [] ->
          Variable.print key Format.str_formatter;
          let var_str = Format.flush_str_formatter () in
          raise (VariableNotFound var_str)
      | VarMap map :: rest -> (
          match VariableMap.find_opt key map with
          | Some value -> value
          | None -> find_in_maps rest)
      | Tau _ :: rest -> find_in_maps rest
    in
    find_in_maps lst

  let find_variable_opt (key : Variable.t) (lst : 'a t) : 'a option =
    let rec find_in_maps maps =
      match maps with
      | [] -> None
      | VarMap map :: rest -> (
          match VariableMap.find_opt key map with
          | Some value -> Some value
          | None -> find_in_maps rest)
      | Tau _ :: rest -> find_in_maps rest
    in
    find_in_maps lst

  let abstract_tau_sum (lst : 'a t) : tau =
    let rec sum acc = function
      | [] -> acc
      | Tau n :: rest -> sum (TauAdd (acc, n)) rest
      | VarMap _ :: rest -> sum acc rest
    in
    sum (TauConst 0) lst

  let rec eval_tau t =
    match t with
    | TauConst c -> c
    | TauParam _ -> Error.typing "TauParam not supported in eval_tau"
    | TauAdd (t1, t2) -> eval_tau t1 + eval_tau t2

  let subtract_tau (tau : tau) (lst : 'a t) : 'a t =
    let rec subtract remaining target =
      match (remaining, target) with
      | rem, 0 -> rem
      | [], _ -> Error.typing "Not enough tau to subtract"
      | VarMap _ :: rest, _ -> subtract rest target
      | Tau t :: rest, tgt_val ->
          let t_val = eval_tau t in
          if tgt_val > t_val then subtract rest (tgt_val - t_val)
          else
            let remaining_tau = TauConst (t_val - tgt_val) in
            Tau remaining_tau :: rest
    in
    subtract lst (eval_tau tau)
end
