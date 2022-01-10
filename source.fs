module script1

type Prop =
    | False
    | True
    | Atom of string
    | Not of Prop
    | And of Prop * Prop
    | Or of Prop * Prop
    | Imp of Prop * Prop
    | Iff of Prop * Prop

type Question = Q of Prop list * Prop * string list

type tfpair = struct
    val tf : bool
    val symbol : string
end

type Discrete = tfpair list


let rec find_strings1 (input: Prop) : string list = 
    match input with 
    | False -> []
    | True -> []
    | Atom string -> [string]
    | Not prop -> find_strings1 prop
    | And (prop1, prop2) -> find_strings1 prop1 @ find_strings1 prop2
    | Or (prop1, prop2) -> find_strings1 prop1 @ find_strings1 prop2
    | Imp (prop1, prop2) -> find_strings1 prop1 @ find_strings1 prop2
    | Iff (prop1, prop2) -> find_strings1 prop1 @ find_strings1 prop2

let find_strings (input: Prop) : string list = 
    input |> find_strings1 |> List.distinct

let rec print_prop1 (input: Prop) : string = 
    match input with 
    | False -> "falsum"
    | True -> "true"
    | Atom string -> string
    | Not prop -> "not " + print_prop1 prop
    | And (prop1, prop2) -> "(" + print_prop1 prop1 + " and " + print_prop1 prop2 + ")"
    | Or (prop1, prop2) -> "(" + print_prop1 prop1 + " or " + print_prop1 prop2 + ")"
    | Imp (prop1, prop2) -> "(" + print_prop1 prop1 + " implies " + print_prop1 prop2 + ")"
    | Iff (prop1, prop2) -> "(" + print_prop1 prop1 + " iff " + print_prop1 prop2 + ")"

let print_prop2 (input: Prop) : string = 
    match input with 
    | False -> "falsum"
    | True -> "true"
    | Atom string -> string
    | Not prop -> "It is not the case that " + print_prop1 prop
    | And (prop1, prop2) -> print_prop1 prop1 + " and " + print_prop1 prop2 
    | Or (prop1, prop2) ->  "Either " + print_prop1 prop1 + " or " + print_prop1 prop2 
    | Imp (prop1, prop2) -> "If " + print_prop1 prop1 + " then " + print_prop1 prop2 
    | Iff (prop1, prop2) -> print_prop1 prop1 + " if and only if " + print_prop1 prop2 

let cap (input:string): string = 
    string (Char.ToUpper(input.[0])) + input.[1..] + "."

let print_prop (input: Prop) : string = 
    input |> print_prop2 |> cap

let rec symb_prop1 (input: Prop) : string = 
    match input with 
    | False -> "falsum"
    | True -> "true"
    | Atom string -> string
    | Not prop -> "~ " + symb_prop1 prop
    | And (prop1, prop2) -> "(" + symb_prop1 prop1 + " /\ " + symb_prop1 prop2 + ")"
    | Or (prop1, prop2) -> "(" + symb_prop1 prop1 + " \/ " + symb_prop1 prop2 + ")"
    | Imp (prop1, prop2) -> "(" + symb_prop1 prop1 + " -> " + symb_prop1 prop2 + ")"
    | Iff (prop1, prop2) -> "(" + symb_prop1 prop1 + " <-> " + symb_prop1 prop2 + ")"

let symb_prop (input: Prop) : string = 
    match input with 
    | False -> "falsum"
    | True -> "true"
    | Atom string -> string
    | Not prop -> "~ " + symb_prop1 prop
    | And (prop1, prop2) -> symb_prop1 prop1 + " /\ " + symb_prop1 prop2 
    | Or (prop1, prop2) ->  symb_prop1 prop1 + " \/ " + symb_prop1 prop2 
    | Imp (prop1, prop2) ->  symb_prop1 prop1 + " -> " + symb_prop1 prop2 
    | Iff (prop1, prop2) -> symb_prop1 prop1 + " <-> " + symb_prop1 prop2 

let rec create_bool (dim:int) (seed:int) (current: bool list) : bool list = 
    if dim = 0 then current
    elif seed >= pown 2 (dim-1) then create_bool (dim-1) (seed - pown 2 (dim-1)) (true::current)
    else create_bool (dim-1) seed (false::current)

let create_boolray (dim: int) : bool list list = 
    List.map (fun x -> (create_bool dim x [])) [0..(pown 2 dim-1)]

    
let rec solve (input: Prop) (symbols: string list) (valuation: bool list) : bool = 
    if symbols.Length <> valuation.Length then failwith "prop and valuation of diff length"
    else match input with
        | False -> false
        | True -> true
        | Atom string -> valuation.[List.findIndex (fun x -> (x = string)) symbols]
        | Not prop -> not (solve prop symbols valuation)
        | And (prop1, prop2) -> (solve prop1 symbols valuation) && (solve prop2 symbols valuation)
        | Or (prop1, prop2) -> (solve prop1 symbols valuation) || (solve prop2 symbols valuation)
        | Imp (prop1, prop2) -> (not (solve prop1 symbols valuation)) || (solve prop2 symbols valuation)
        | Iff (prop1, prop2) -> ((solve prop1 symbols valuation) && (solve prop2 symbols valuation)) || (not ((solve prop1 symbols valuation) || (solve prop2 symbols valuation)))

let is_tautology (input: Prop) (symbols: string list) : bool =
    let boolray = create_boolray symbols.Length
    if (List.tryFind (fun valuation -> not(solve input symbols valuation)) boolray) = None then true else false

let print_ques (question: Question) : string = 
    match question with 
    | Q (prem, conc, _) -> (String.concat "\n" (List.map (fun i -> "Premise " + i.ToString() + ": " + (print_prop (prem.[i-1]))) [1..prem.Length] )) + "\nConclusion : " + print_prop (conc) 

let print_ques_inline (question: Question) : string = 
    match question with 
    | Q (prem, conc, _) -> (String.concat " " (List.map (fun i -> "Premise " + i.ToString() + ": " + (print_prop (prem.[i-1]))) [1..prem.Length] )) + " Conclusion : " + print_prop (conc) 

let combine_prem (premises : Prop list) : Prop = 
    List.fold (fun x y -> And(x, y)) True premises

let answer_ques (question: Question) : bool = 
    match question with
    | Q (prem, conc, symbols) -> is_tautology (Imp( combine_prem prem , conc)) symbols


(*type Proof = 
    | *)