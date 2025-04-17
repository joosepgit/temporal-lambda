module TauParamModule = Symbol.Make ()
module TauParamMap = Map.Make (TauParamModule)
module TauParamSet = Set.Make (TauParamModule)
module TauPrintParam = Print.TauPrintParam (TauParamMap)
module TyParamModule = Symbol.Make ()
module TyParamMap = Map.Make (TyParamModule)
module TyParamSet = Set.Make (TyParamModule)
module TyPrintParam = Print.TyPrintParam (TyParamMap)

type tau_param = TauParamModule.t
type ty_param = TyParamModule.t
type tau = TauConst of int | TauParam of tau_param | TauAdd of tau * tau

module Make
    (Variable : Symbol.S)
    (VariableMap : Map.S with type key = Variable.t) =
struct
  type 'a map_or_tau = VarMap of 'a VariableMap.t | Tau of tau
  type 'a t = 'a map_or_tau list

  let empty : 'a t = []

  (* Add a temporal value to the end of the list in reverse order (by adding to the front) *)
  let add_temp (n : tau) (lst : 'a t) : 'a t = Tau n :: lst

  (* Add a variable to the last VariableMap or create a new one, in reverse order *)
  let add_variable (key : Variable.t) (value : 'a) (lst : 'a t) : 'a t =
    match lst with
    | VarMap map :: rest ->
        (* Add the variable to the last VariableMap *)
        let updated_map = VariableMap.add key value map in
        VarMap updated_map :: rest
    | _ ->
        (* Create a new VariableMap if the last element is not a VarMap *)
        let new_map = VariableMap.add key value VariableMap.empty in
        VarMap new_map :: lst

  (* Find a variable in any VariableMap in the list, in reverse order *)
  let find_variable (key : Variable.t) (lst : 'a t) : 'a =
    let rec find_in_maps maps =
      match maps with
      | [] -> raise Not_found (* No more maps to check *)
      | VarMap map :: rest -> (
          (* Check if the key is in this VariableMap *)
          match VariableMap.find_opt key map with
          | Some value -> value (* Found the variable *)
          | None ->
              find_in_maps rest (* Continue searching in the rest of the list *)
          )
      | Tau _ :: rest -> find_in_maps rest (* Skip Nat elements *)
    in
    find_in_maps lst

  (* Find a variable in any VariableMap in the list, in reverse order *)
  let find_variable_opt (key : Variable.t) (lst : 'a t) : 'a option =
    let rec find_in_maps maps =
      match maps with
      | [] -> None (* No more maps to check *)
      | VarMap map :: rest -> (
          (* Check if the key is in this VariableMap *)
          match VariableMap.find_opt key map with
          | Some value -> Some value (* Found the variable *)
          | None ->
              find_in_maps rest (* Continue searching in the rest of the list *)
          )
      | Tau _ :: rest -> find_in_maps rest (* Skip Nat elements *)
    in
    find_in_maps lst

  let rec eval_tau t =
    match t with
    | TauConst c -> c
    | TauParam _ -> Error.typing "TauParam not supported in eval_tau"
    | TauAdd (t1, t2) -> eval_tau t1 + eval_tau t2

  let tau_sum (lst : 'a t) : int =
    let rec sum acc = function
      | [] -> acc
      | Tau n :: rest -> sum (acc + eval_tau n) rest
      | VarMap _ :: rest -> sum acc rest
    in
    sum 0 lst

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

  (* Print tau abstractions *)
  let rec print_tau ?max_level tau_pp tau ppf =
    let print ?at_level = Print.print ?max_level ?at_level ppf in
    match tau with
    | TauConst i -> Format.fprintf ppf "%d" i
    | TauParam p -> print "%t" (tau_pp p)
    | TauAdd (t1, t2) ->
        Format.fprintf ppf "@[%t + %t@]"
          (fun ppf -> print_tau tau_pp t1 ppf)
          (fun ppf -> print_tau tau_pp t2 ppf)

  (* Print the contents of the list, reversing it before printing *)
  let print_contents print_var_and_ty lst =
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
    let ppf = Format.std_formatter in
    Print.print ppf "VariableContext: [\n";
    (* Reverse the list before printing *)
    print_list (List.rev lst) ppf;
    Print.print ppf "]\n"
end
