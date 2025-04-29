(** Pretty-printing functions *)

let rec subscript i =
  let last =
    List.nth
      [
        "\226\130\128";
        "\226\130\129";
        "\226\130\130";
        "\226\130\131";
        "\226\130\132";
        "\226\130\133";
        "\226\130\134";
        "\226\130\135";
        "\226\130\136";
        "\226\130\137";
      ]
      (i mod 10)
  in
  if i < 10 then last else subscript (i / 10) ^ last

let greek_letters =
  [|
    "α";
    "β";
    "γ";
    "δ";
    "ε";
    "ζ";
    "η";
    "θ";
    "ι";
    "κ";
    "λ";
    "μ";
    "ν";
    "ξ";
    "ο";
    "π";
    "ρ";
    "σ";
  |]

let type_symbol n =
  if n < Array.length greek_letters then greek_letters.(n)
  else "σ" ^ subscript (n - Array.length greek_letters)

let tau_symbol n = "τ" ^ subscript n

module TyPrintParam (ParamMap : Map.S) = struct
  let create () =
    let names = ref ParamMap.empty in
    let counter = ref 0 in
    let print_param param ppf =
      let symbol =
        match ParamMap.find_opt param !names with
        | Some symbol -> symbol
        | None ->
            let symbol = type_symbol !counter in
            incr counter;
            names := ParamMap.add param symbol !names;
            symbol
      in
      Format.fprintf ppf "%s" symbol
    in
    print_param
end

module TauPrintParam (ParamMap : Map.S) = struct
  let create () =
    let names = ref ParamMap.empty in
    let counter = ref 0 in
    let print_param param ppf =
      let symbol =
        match ParamMap.find_opt param !names with
        | Some symbol -> symbol
        | None ->
            let symbol = tau_symbol !counter in
            incr counter;
            names := ParamMap.add param symbol !names;
            symbol
      in
      Format.fprintf ppf "%s" symbol
    in
    print_param
end

let message ?loc ~header fmt =
  match loc with
  | Some loc ->
      Format.fprintf Format.err_formatter
        ("%s (%t):@," ^^ fmt ^^ "@.")
        header (Location.print loc)
  | _ -> Format.fprintf Format.err_formatter ("%s: " ^^ fmt ^^ "@.") header

let error ?loc err_kind fmt = message ?loc ~header:err_kind fmt
let check ?loc fmt = message ?loc ~header:"Check" fmt
let warning ?loc fmt = message ?loc ~header:"Warning" fmt
let debug ?loc fmt = message ?loc ~header:"Debug" fmt

let print ?(at_level = min_int) ?(max_level = max_int) ppf =
  if at_level <= max_level then Format.fprintf ppf
  else fun fmt -> Format.fprintf ppf ("(" ^^ fmt ^^ ")")

let rec print_sequence sep pp vs ppf =
  match vs with
  | [] -> ()
  | [ v ] -> pp v ppf
  | v :: vs ->
      Format.fprintf ppf "%t%s@,%t" (pp v) sep (print_sequence sep pp vs)

let rec print_cases pp vs ppf =
  match vs with
  | [] -> ()
  | [ v ] -> pp v ppf
  | v :: vs -> Format.fprintf ppf "%t@,| %t" (pp v) (print_cases pp vs)

let print_field fpp vpp (f, v) ppf = print ppf "%t = %t" (fpp f) (vpp v)

let print_tuple pp lst ppf =
  match lst with
  | [] -> print ppf "()"
  | lst -> print ppf "(@[<hov>%t@])" (print_sequence ", " pp lst)

let print_record fpp vpp assoc ppf =
  print ppf "{@[<hov>%t@]}" (print_sequence "; " (print_field fpp vpp) assoc)
