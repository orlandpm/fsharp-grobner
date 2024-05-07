
#load "BigRationals.fsx"

open BigRationals

type Monomial = 
    {
        Coefficient : BigRational
        Powers : int list
    }
    override x.ToString() = // default variable choices are x, xy, xyz, wxyz, vwxyz, etc.
        let vars = 
            ["r";"s";"t";"u";"v";"w";"x";"y";"z"]
            |> List.rev
            |> List.skip (3-x.Powers.Length)
            |> List.take x.Powers.Length
            |> List.rev
        List.zip vars x.Powers
        |> List.filter (snd >> ((<>) 0))
        |> List.map (fun (x,p) -> if p = 1 then x else sprintf "%s^%d" x p)
        |> String.concat " "
        |> fun monomials -> 
            if x.Coefficient = rational 1 then 
                if List.sum x.Powers = 0 then "1" else monomials 
            else 
                sprintf "%O %s" x.Coefficient monomials

    member x.Degree = 
        List.sum x.Powers

type MonomialOrder = Monomial -> Monomial -> int

let combineLikeTerms (mons:Monomial list) =
    mons
    |> List.groupBy (fun mon -> mon.Powers)
    |> List.map (fun (pows,mons) -> 
        let coeff = mons |> List.sumBy (fun mon -> mon.Coefficient)
        { Coefficient = coeff; Powers = pows}
    )
    |> List.filter (fun mon -> mon.Coefficient <> rational 0)

type Polynomial =
    {
        Terms : Monomial list
    }
    override x.ToString() =
        if x.Terms.IsEmpty then "0" else
            x.Terms
            |> List.map (fun t -> t.ToString())
            |> String.concat " + "

    static member (+) (p1:Polynomial, p2:Polynomial) =
        List.append p1.Terms p2.Terms
        |> combineLikeTerms
        |> fun mons -> {Terms = mons}

    static member (-) (p1:Polynomial, p2:Polynomial) =
        p2.Terms
        |> List.map (fun mon -> {mon with Coefficient = -mon.Coefficient})
        |> List.append p1.Terms 
        |> combineLikeTerms
        |> fun mons -> {Terms = mons}

    static member (*) (p1:Polynomial, p2:Polynomial) =
        p1.Terms
        |> List.collect (fun t1 ->
            p2.Terms
            |> List.map (fun t2 ->
                { 
                    Coefficient = t1.Coefficient * (t2.Coefficient)
                    Powers = List.map2 (+) t1.Powers t2.Powers
                }
            )
        )
        |> combineLikeTerms
        |> fun mons -> {Terms = mons}

let mon (pows:int list) = 
    {
        Coefficient = rational 1
        Powers = pows
    }

let var deg idx =
    [0..deg-1]
    |> List.map (fun i -> if i = idx then 1 else 0)
    |> mon


let poly (terms:(int*(int list)) list) = 
    terms
    |> List.map (fun (coeff,pows) -> {Coefficient = rational coeff; Powers = pows})
    |> fun ts -> { Terms = ts }


module Monomial =
    let sort (order:MonomialOrder) (mons:Monomial list) =
        mons
        |> List.sortWith order

    let divides (m1:Monomial) (m2:Monomial) =
        List.zip m1.Powers m2.Powers
        |> List.forall (fun (pow1,pow2) -> pow1 <= pow2)
        || m2.Coefficient = rational 0

    let divide (m1:Monomial) (m2:Monomial) =
        {
            Coefficient = m1.Coefficient / m2.Coefficient
            Powers = List.zip m1.Powers m2.Powers |> List.map (fun (p1,p2) -> p1-p2)
        }

    let lcm (m1:Monomial) (m2:Monomial) =
        {
            Coefficient = rational 1
            Powers = List.map2 max m1.Powers m2.Powers
        }

let lex (m1:Monomial) (m2:Monomial) =
    List.map2 (-) m1.Powers m2.Powers
    |> List.tryFind ((<>) 0)
    |> Option.defaultValue 0
    |> fun sign -> -sign


let customLex (varOrder:string list) (m1:Monomial) (m2:Monomial) =
    let defaultOrder = List.sort varOrder
    let indices = varOrder |> List.map (fun v -> List.findIndex ((=) v) defaultOrder)
    let sortedPowers1 = indices |> List.map (fun i -> m1.Powers[i])
    let sortedPowers2 = indices |> List.map (fun i -> m2.Powers[i])
    List.map2 (-) sortedPowers1 sortedPowers2
    |> List.tryFind ((<>) 0)
    |> Option.defaultValue 0
    |> fun sign -> -sign


let grlex (m1:Monomial) (m2:Monomial) =
    if m1.Degree < m2.Degree then 1
    elif m2.Degree > m2.Degree then -1
    else lex m1 m2


let mapNth<'T> (n:int) (transform: 'T -> 'T) (lst :'T list) =
    lst
    |> List.indexed
    |> List.map (fun (idx,lst) ->
        if idx = n then transform lst else lst
    )

assert (Monomial.sort lex [mon [1;2;0]; mon [0;3;4]] = [mon [1;2;0]; mon [0;3;4]])  // p 56
assert (Monomial.sort lex [mon [3;2;4]; mon [3;2;1]] = [mon [3;2;4]; mon [3;2;1]])  // p 56
assert ([0..5]                                  // p 56
        |> List.map (fun idx -> var 6 idx)
        |> fun x -> x = Monomial.sort lex x)
assert (Monomial.sort grlex [mon [1;2;3]; mon [3;2;0]] = [mon [1;2;3]; mon [3;2;0]]) // p 58
assert (Monomial.sort grlex [mon [5;1;1]; mon [4;1;2]] = [mon [5;1;1]; mon [4;1;2]]) // p 59


module Polynomial =

    let ofMonomial (m:Monomial) =
        {Terms = [m]}

    let sortTerms (order: MonomialOrder) (poly:Polynomial) : Polynomial =
        { Terms = Monomial.sort order poly.Terms}

    let multidegree order (f:Polynomial) =
        Monomial.sort order f.Terms
        |> List.head
        |> fun t -> t.Powers

    let lc order (f:Polynomial) : BigRational =
        Monomial.sort order f.Terms
        |> List.head
        |> fun t -> t.Coefficient

    let lm order f : Monomial =
        mon (multidegree order f)

    let lt order f : Monomial =
        Monomial.sort order f.Terms
        |> List.head

    let zero = poly []

    let scale (r:BigRational) (p:Polynomial) =
        p.Terms
        |> List.map (fun mon ->
             {mon with Coefficient = r * mon.Coefficient})
        |> fun terms -> {Terms=terms}

    let rec divideRec (o:MonomialOrder) (fs:Polynomial list) (p:Polynomial) (qacc:Polynomial list) (racc:Polynomial) =
        if p.Terms.Length = 0 then
            qacc, racc
        else
            let ltp = (lt o p)
            let leadingTermDivides =
                fs
                |> List.tryFindIndex (fun fi ->
                    Monomial.divides (lt o fi) ltp
                )
            match leadingTermDivides with
            | Some idx ->
                let f = fs[idx]
                // printfn "LT(%O) | LT(%O)" (f) (p)
                let quotient = 
                    Monomial.divide ltp (lt o f)
                    |> ofMonomial
                // printfn "quotient is %O" quotient
                let pNext = p - (quotient * f)
                // printfn "subtracting %O from %O yields %O" (quotient * f) p pNext
                let qaccNext = mapNth idx (fun x -> x + quotient) qacc
                // printfn "quotients are currently %O" qaccNext
                divideRec o fs pNext qaccNext racc
            | None -> 
                // printfn "no leading term divides LT(%O); sending to remainder" p
                let ltpPoly = ofMonomial(ltp)
                divideRec o fs (p - ltpPoly) qacc (racc + ltpPoly)

    let divide o fs p =
        divideRec o fs p [for fi in fs -> zero] zero

    let remainder o fs p =
        divide o fs p |> snd

// let f = poly [4,[1;2;1]; 4,[0;0;2]; -5,[3;0;0]; 7,[2;0;2]] // page 60
// Polynomial.multidegree lex f // page 60
// Polynomial.lc lex f // page 60
// Polynomial.lm lex f |> string // page 60
// Polynomial.lt lex f |> string // page 60
// Monomial.divides (mon [0;1;1]) (mon [1;2;1])


let oneVarPoly (nVars: int) (i:int) =
    poly [1,[for j in 0..nVars-1 -> if i=j then 1 else 0]] 


let oneVarPolys (nVars) =
    [0..nVars-1] 
    |> List.map (oneVarPoly nVars)


let p62Example() = 
    let f = poly [1,[1;2]; 1,[0;0]]
    let f1 = poly [1,[1;1]; 1,[0;0]]
    let f2 = poly [1,[0;1]; 1,[0;0]]

    Polynomial.divide lex [f1;f2] f
    |> printfn "%O"


let p63Example() = 
    let f = poly [1,[2;1]; 1,[1;2] ; 1,[0;2]]
    let f1 = poly [1,[1;1]; -1,[0;0]]
    let f2 = poly [1,[0;2]; -1,[0;0]] 
    printfn "dividing %O by %O and %O" f f1 f2

    Polynomial.divide lex [f1;f2] f
    |> printfn "%O"


let p67Example() = 
    let f = poly [1,[2;1]; 1,[1;2] ; 1,[0;2]]
    let f2 = poly [1,[1;1]; -1,[0;0]]
    let f1 = poly [1,[0;2]; -1,[0;0]] 
    printfn "dividing %O by %O and %O" f f1 f2

    Polynomial.divide lex [f1;f2] f
    |> printfn "%O"


let sPolynomial (o:MonomialOrder) (f:Polynomial) (g:Polynomial) =
    let ltf = Polynomial.lt o f
    let ltg = Polynomial.lt o g
    let lcm = Monomial.lcm ltf ltg
    (Monomial.divide lcm ltf |> Polynomial.ofMonomial) * f 
        - (Monomial.divide lcm ltg |> Polynomial.ofMonomial) * g


let p85Example() = 
    let f = poly [1,[3;2]; -1,[2;3]]
    printfn "%O" f
    let g = poly [3,[4;1]; 1,[0;2]]
    printfn "%O" g

    printfn "S Polynomial w.r.t. grlex is %O" (sPolynomial grlex f g)


let p90Example() =
    let f1 = poly [1,[3;0]; -2,[1;1]]
    let f2 = poly [1,[2;1]; -2,[0;2]; 1,[1;0]]
    let f3 = sPolynomial grlex f1 f2

    let f123 = [f1;f2;f3]
    printfn "not a Grobner basis since LT(S(f1,f2)) = %O" <| Polynomial.lt grlex f3

    let _, f3Modf123 = Polynomial.divide grlex f123 f3
    printfn "f3 mod f123 is %O" f3Modf123

    let sf1f3 = sPolynomial grlex f1 f3
    printfn "sf1f3 = %O" sf1f3
    printfn "sf1f3 Mod f123 = %O" (Polynomial.remainder grlex f123 sf1f3)

    let f4 = sf1f3

    let f1234 = [f1;f2;f3;f4]

    sPolynomial grlex f1 f4 |> string

    sPolynomial grlex f2 f3 |> string

    let f5 = 
        sPolynomial grlex f2 f3
        |> Polynomial.remainder grlex f1234

    let f12345 = [f1;f2;f3;f4;f5]

    List.allPairs f12345 f12345
    |> List.map (fun (fi,fj) ->
        (sPolynomial grlex fi fj) 
        |> Polynomial.remainder grlex f12345 
    )
    |> List.iter (fun p -> printfn "%O" p)


let rec grobnerBasis (o:MonomialOrder) (fs:Polynomial list) = 
    printfn "%d basis vectors" (fs.Length)
    let newGenerators =
        List.allPairs fs fs
        |> List.choose (fun (fi, fj) -> 
            if fi = fj then None 
            else
                let r = 
                    sPolynomial o fi fj
                    |> Polynomial.remainder o fs
                if r = Polynomial.zero then None else Some r
        )
    match newGenerators with
    | [] -> fs
    | _ -> grobnerBasis o (fs @ newGenerators)


let redoP90Example() =
    let f1 = poly [1,[3;0]; -2,[1;1]]
    let f2 = poly [1,[2;1]; -2,[0;2]; 1,[1;0]]

    let basis = grobnerBasis grlex [f1;f2]

    printfn "GROBNER BASIS IS:"
    List.iter (printfn "%O") basis

redoP90Example()


let rec minimizeGrobnerBasis (o:MonomialOrder) (fs:Polynomial list) =   
    match fs with
    | [] -> []
    | fi :: rest ->
        let redundant = 
            rest
            |> List.exists (fun fj -> 
                Monomial.divides (Polynomial.lt o fj) (Polynomial.lt o fi)
            )
        if redundant then
            minimizeGrobnerBasis o rest
        else
            let lc = Polynomial.lc o fi
            // printfn "lc of %O is %O" fi lc
            Polynomial.scale (rational 1 / lc) fi :: minimizeGrobnerBasis o rest


let reduceGrobnerBasis (o:MonomialOrder) (basis:Polynomial list) =
    let minBasis = 
        basis
        |> minimizeGrobnerBasis o

    minBasis
    |> List.mapi (fun i p -> 
        let rest = (minBasis |> List.take i) @ (minBasis |> List.skip (i+1))
        Polynomial.remainder o rest p
    )
    |> List.map (Polynomial.sortTerms lex)

let reduceP90Example() =
    let f1 = poly [1,[3;0]; -2,[1;1]]
    let f2 = poly [1,[2;1]; -2,[0;2]; 1,[1;0]]

    let basis = 
        grobnerBasis grlex [f1;f2]
        |> minimizeGrobnerBasis grlex

    printfn "GROBNER BASIS IS:"
    List.iter (printfn "%O") basis

reduceP90Example()


let cmuExample() =
    let [x;y;z] = oneVarPolys 3
    let f1 = x*x - y
    let f2 = x*x*x-z
    grobnerBasis lex [f1;f2]
cmuExample()
|> minimizeGrobnerBasis lex


// let cmuExamplePage6() =
//     let [x;y] = oneVarPolys 2
//     let f1 = y*y + y*x + x*x
//     let f2 = y + x
//     let f3 = y
//     let f4 = x*x
//     let f5 = x

//     let gb = 
//         // grobnerBasis lex [f1;f2;f3;f4;f5]
//         // [y+x; x]
//         // |> minimizeGrobnerBasis lex
//         |> reduceGrobnerBasis lex

//     // printfn "grobner basis:"
//     // |> List.iter (printfn "%O")

//     gb
//     |> List.iter (printfn "%O")
// cmuExamplePage6()


let p99Example() =
    let [w;x;y;z] = oneVarPolys 4 // w = lambda
    let cnst r = poly [r,[0;0;0;0]]

    let fs = [
        x*x + (cnst 2) * y * z -  (cnst 2) * x * w
        (cnst 2) * x * z - (cnst 2) * y * w
        (cnst 2) * x * y - (cnst 2) * z - (cnst 2) * z * w
        x*x + y*y + z*z - (cnst 1)
    ]
    fs
    |> List.iter (printfn "%O")

    let basis = grobnerBasis lex fs
    // |> minimizeGrobnerBasis lex

    let reduced = reduceGrobnerBasis lex basis
    reduced
    |> List.iter (printfn "%O")

    reduced
p99Example()


let hw2problem2() =
    let [x;y] = oneVarPolys 2
    let cnst r = poly [r,[0;0]]
    let f1 = x*x - x*y - (cnst 2) * x
    let f2 = y*y - (cnst 2)*x*y - y
    printfn "f1 = %O" f1
    printfn "f2 = %O" f2
    let order = customLex ["y";"x"]

    printfn "grobner basis:"
    grobnerBasis order [f1;f2]
    |> reduceGrobnerBasis order
    |> List.map (Polynomial.sortTerms order)
    |> List.iter (printfn "%O")
    
hw2problem2()


let hw2problem3() =
    let [u;v;_;x;y;z] = oneVarPolys 6
    printfn "vars"
    for var in [u;v;x;y;z] do printfn "%O" var
    let cnst r = poly [r,[0;0;0;0;0;0]]

    let f1 = u - x - (cnst 2) * v
    let f2 = u*v - y
    let f3 = v - z

    printfn "f1 = %O" f1
    printfn "f2 = %O" f2
    printfn "f3 = %O" f3

    printfn "grobner basis:"
    grobnerBasis lex [f1;f2;f3]
    |> reduceGrobnerBasis lex
    |> List.map (Polynomial.sortTerms lex)
    |> List.iter (printfn "%O")
    
hw2problem3()