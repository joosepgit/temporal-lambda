module Make
    (Variable : Symbol.S)
    (VariableMap : Map.S with type key = Variable.t) =
struct
  type 'a map_or_tau = VarMap of 'a VariableMap.t | Nat of int
  type 'a t = 'a map_or_tau list

  let empty : 'a t = []

  (* Add a natural number to the end of the list in reverse order (by adding to the front) *)
  let add_temp (n : int) (lst : 'a t) : 'a t = Nat n :: lst

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
      | Nat _ :: rest -> find_in_maps rest (* Skip Nat elements *)
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
      | Nat _ :: rest -> find_in_maps rest (* Skip Nat elements *)
    in
    find_in_maps lst

  (* Print the contents of the list, reversing it before printing *)
  let print_contents print_var_and_ty lst =
    let rec print_list lst =
      match lst with
      | [] -> ()
      | VarMap map :: rest ->
          Printf.printf "VarMap: {\n";
          let elements = VariableMap.bindings map in
          let rec print_elements = function
            | [] -> ()
            | [ entry ] ->
                (* Last element: no trailing semicolon *)
                Printf.printf "(";
                print_var_and_ty entry Format.std_formatter;
                Printf.printf ")"
            | entry :: tl ->
                (* All other elements: add semicolon *)
                Printf.printf "(";
                print_var_and_ty entry Format.std_formatter;
                Printf.printf "), ";
                print_elements tl
          in
          print_elements elements;
          Printf.printf "}\n";
          print_list rest
      | Nat n :: rest ->
          Printf.printf "Nat %d\n" n;
          print_list rest
    in
    (* Reverse the list before printing *)
    print_list (List.rev lst)
end
