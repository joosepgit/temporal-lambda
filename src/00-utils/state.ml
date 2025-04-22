module Make
    (Resource : Symbol.S)
    (ResourceMap : Map.S with type key = Resource.t) =
struct
  type 'a map_or_tau = ResourceMap of 'a ResourceMap.t | Tau of Context.tau
  type 'a t = 'a map_or_tau list

  let empty : 'a t = []
  let add_temp (n : Context.tau) (lst : 'a t) : 'a t = Tau n :: lst

  let add_resource (key : Resource.t) (value : 'a) (lst : 'a t) : 'a t =
    match lst with
    | ResourceMap map :: rest ->
        let updated_map = ResourceMap.add key value map in
        ResourceMap updated_map :: rest
    | _ ->
        let new_map = ResourceMap.add key value ResourceMap.empty in
        ResourceMap new_map :: lst

  let find_resource (key : Resource.t) (lst : 'a t) : 'a =
    let rec find_in_maps maps =
      match maps with
      | [] ->
          Resource.print key Format.str_formatter;
          let var_str = Format.flush_str_formatter () in
          raise (Context.VariableNotFound var_str)
      | ResourceMap map :: rest -> (
          match ResourceMap.find_opt key map with
          | Some value -> value
          | None -> find_in_maps rest)
      | Tau _ :: rest -> find_in_maps rest
    in
    find_in_maps lst
end
