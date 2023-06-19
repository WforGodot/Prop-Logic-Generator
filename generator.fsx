open System
open System.IO

#load "source.fs"
open script1

let random = System.Random()
let a () = random.Next(1, 300)
let max_seed = 9771
let randlist = List.map (fun x -> a()) [1..max_seed] 
let mutable seed = 609

let rd (max : int) = 
    seed <- (seed + 1)%977100
    (randlist.[seed%max_seed] + seed)%max


let rec generate_prop (symbols: string list) (length: int) : Prop = 

    if length = 1 then 
        let r = rd(3)
        let s = rd(symbols.Length)
        if r < 2 then Atom (symbols.[s]) else Not (Atom (symbols.[s]))
    else 
        let r = rd(17)
        let s = rd(length - 1) + 1
        
        let t = length - s
        if r < 4 then And(generate_prop symbols s , generate_prop symbols t)
        elif r < 8 then Or(generate_prop symbols s , generate_prop symbols t)
        elif r < 12 then Imp(generate_prop symbols s , generate_prop symbols t)
        elif r < 13 then Iff(generate_prop symbols s, generate_prop symbols t)
        else Not(generate_prop symbols (length-1))


let rec generate_ques (symbols: string list) (premise_count: int) (max_length: int) (conc_length:int) : Question =
    let prem_list = List.map (fun i -> generate_prop symbols (rd(max_length)+1) ) [1..premise_count]
    let conc = generate_prop symbols (rd(conc_length)+1)
    Q (prem_list, conc, symbols)

let rec rand_var (length: int) : string list = 
    List.map (fun x -> (rd(26/length) + (x*26)/length + 65)|>char |> Char.ToUpper |> string ) [0..length-1]
   
    
let ques_list = List.map (fun i -> (generate_ques (rand_var 2) 2 2 2)) [1..3000]
let ques_list2 = List.distinct ques_list

let writer = new System.IO.StreamWriter("trivial3.csv")
writer.Write ("Question;target\n")

let mutable no_true = 0

for quesy in ques_list2 do 
    writer.WriteLine ((print_ques_inline quesy) + ";" + string(System.Convert.ToInt32(answer_ques quesy)))
    if (answer_ques quesy) then no_true <- no_true + 1

writer.Close()
printfn "%d %d" ques_list.Length ques_list2.Length
printfn "%d" no_true




