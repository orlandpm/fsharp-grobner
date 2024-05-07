let rec gcd (x:bigint) (y:bigint) =
    if x = 0I then y else gcd (y % x) x

[<CustomEquality; NoComparison>]
type BigRational = 
    {
        Numerator : bigint
        Denominator : bigint
    }
    member r.Reduce() =
        let d = gcd (abs r.Numerator) (abs r.Denominator)
        let sign = if r.Denominator < 0I then -1I else 1I
        {
            Numerator = sign * r.Numerator / d
            Denominator = sign * r.Denominator / d
        }
    override r.Equals(b) =
        match b with
        | :? BigRational as s -> r.Numerator * s.Denominator = s.Numerator * r.Denominator
        | _ -> false

    static member (+) (r1:BigRational, r2:BigRational) =
        {
            Numerator = r1.Numerator * r2.Denominator + r2.Numerator * r1.Denominator
            Denominator = r1.Denominator * r2.Denominator
        }.Reduce()

    static member (-) (r1:BigRational, r2:BigRational) =
        {
            Numerator = r1.Numerator * r2.Denominator + r2.Numerator * r1.Denominator
            Denominator = r1.Denominator * r2.Denominator
        }.Reduce()
    static member (*) (r1:BigRational,r2:BigRational) =
        {
            Numerator = r1.Numerator * r2.Numerator
            Denominator = r1.Denominator * r2.Denominator
        }.Reduce()

    static member (/) (r1:BigRational,r2:BigRational) =
        {
            Numerator = r1.Numerator * r2.Denominator
            Denominator = r1.Denominator * r2.Numerator
        }.Reduce()

    static member (~-) (r:BigRational) =
        {
            Numerator = -r.Numerator
            Denominator = r.Denominator
        }.Reduce()

    override r.ToString() =
        if r.Denominator = 1I then string r.Numerator else sprintf "(%A/%A)" r.Numerator r.Denominator 

    static member get_Zero() =
        {Numerator =0I; Denominator=1I}
    
    static member Quotient (n:bigint) (d:bigint) = {Numerator=n;Denominator=d}.Reduce()

let rational (i:int) = {Numerator=bigint i; Denominator=bigint 1}