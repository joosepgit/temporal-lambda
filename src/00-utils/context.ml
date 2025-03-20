module TauParamModule = Symbol.Make ()
module TauParamMap = Map.Make (TauParamModule)

type tau_param = TauParamModule.t
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

  (* Print tau abstractions *)
  let rec print_tau print_param tau ppf =
    match tau with
    | TauConst i -> Format.fprintf ppf "TauConst(%d)" i
    | TauParam p -> Format.fprintf ppf "TauParam(%t)" (TauParamModule.print p)
    | TauAdd (t1, t2) ->
        Format.fprintf ppf "TauAdd(@[%t, %t@])"
          (fun ppf -> print_tau print_param t1 ppf)
          (fun ppf -> print_tau print_param t2 ppf)

  (* Print the contents of the list, reversing it before printing *)
  let print_contents print_param print_var_and_ty lst =
    let rec print_list lst ppf =
      match lst with
      | [] -> ()
      | VarMap map :: rest ->
          Print.print ppf "VarMap: {\n";
          let elements = VariableMap.bindings map in
          let rec print_elements = function
            | [] -> ()
            | entry :: tl ->
                print_var_and_ty entry ppf;
                Print.print ppf "\n";
                print_elements tl
          in
          print_elements elements;
          Print.print ppf "}\n";
          print_list rest ppf
      | Tau n :: rest ->
          print_tau print_param n ppf;
          Print.print ppf "\n";
          print_list rest ppf
    in
    let ppf = Format.std_formatter in
    Print.print ppf "VariableContext: [\n";
    (* Reverse the list before printing *)
    print_list (List.rev lst) ppf;
    Print.print ppf "]\n"
end
