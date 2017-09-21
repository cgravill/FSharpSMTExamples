open Microsoft.Z3

let petPurchasing() =
    use context = new Microsoft.Z3.Context()

    let dog = context.MkIntConst("dog")
    let cat = context.MkIntConst("cat")
    let mouse = context.MkIntConst("mouse")

    let dogCost = context.MkMul(context.MkInt(1500), dog)
    let catCost = context.MkMul(context.MkInt(100), cat)
    let mouseCost = context.MkMul(context.MkInt(25), mouse)

    let solver = context.MkSolver()
    solver.Assert(context.MkGe(dog,context.MkInt(1)))
    solver.Assert(context.MkGe(cat,context.MkInt(1)))
    solver.Assert(context.MkGe(mouse,context.MkInt(1)))
    
    let exp = context.MkAdd(dogCost, catCost, mouseCost)

    solver.Assert(context.MkEq(context.MkInt(10000), exp))

    let status = solver.Check()

    match status with
    | Status.SATISFIABLE ->
            printfn "dogs: %s, cats: %s, mice: %s"
                (solver.Model.Eval(dog, true).ToString())
                (solver.Model.Eval(cat, true).ToString())
                (solver.Model.Eval(mouse, true).ToString())
    | _ -> printfn "UNSAT" 

type riverState = {
    farmer:BoolExpr
    farmerBoat:BoolExpr
    farmerAcross:BoolExpr
    wolf:BoolExpr
    wolfBoat:BoolExpr
    wolfAcross:BoolExpr
    goat:BoolExpr
    goatBoat:BoolExpr
    goatAcross:BoolExpr
    cabbage:BoolExpr
    cabbageBoat:BoolExpr
    cabbageAcross:BoolExpr
    }

let riverCrossing() =
    use context = new Microsoft.Z3.Context()

    let MkXor3 b1 b2 b3 =
        context.MkAnd(
            context.MkNot(context.MkAnd(b1, b2)),
            context.MkNot(context.MkAnd(b2, b3)),
            context.MkNot(context.MkAnd(b3, b1)),
            context.MkXor(context.MkXor(b1, b2), b3)
            )

    let makeState i =
        {
            farmer = context.MkBoolConst(i.ToString() + "_1");
            farmerBoat = context.MkBoolConst(i.ToString() + "_2");
            farmerAcross = context.MkBoolConst(i.ToString() + "_3");
            wolf = context.MkBoolConst(i.ToString() + "_4");
            wolfBoat = context.MkBoolConst(i.ToString() + "_5");
            wolfAcross = context.MkBoolConst(i.ToString() + "_6");
            goat= context.MkBoolConst(i.ToString() + "_7");
            goatBoat = context.MkBoolConst(i.ToString() + "_8");
            goatAcross = context.MkBoolConst(i.ToString() + "_9");
            cabbage = context.MkBoolConst(i.ToString() + "_10");
            cabbageBoat = context.MkBoolConst(i.ToString() + "_11");
            cabbageAcross = context.MkBoolConst(i.ToString() + "_12");
            }


    let isValidState (state:riverState) =

        let noEating =
            context.MkNot(
                context.MkOr(
                    context.MkAnd(context.MkNot(state.farmer), state.wolf, state.goat), //Snack time!
                    context.MkAnd(context.MkNot(state.farmerBoat), state.wolfBoat, state.goatBoat),
                    context.MkAnd(context.MkNot(state.farmerAcross), state.wolfAcross, state.goatAcross),
                    context.MkAnd(context.MkNot(state.farmer), state.goat, state.cabbage),
                    context.MkAnd(context.MkNot(state.farmerBoat), state.goatBoat, state.cabbageBoat),
                    context.MkAnd(context.MkNot(state.farmerAcross), state.goatAcross, state.cabbageAcross)
                    )
                )

        let boatCapacity =
            context.MkOr(
                context.MkAnd(context.MkNot(state.farmerBoat), context.MkNot(state.wolfBoat), context.MkNot(state.goatBoat), context.MkNot(state.cabbageBoat)),
                context.MkAnd(state.farmerBoat, context.MkNot(state.wolfBoat), context.MkNot(state.goatBoat), context.MkNot(state.cabbageBoat)),
                context.MkAnd(state.farmerBoat, state.wolfBoat, context.MkNot(state.goatBoat), context.MkNot(state.cabbageBoat)),
                context.MkAnd(state.farmerBoat, context.MkNot(state.wolfBoat), state.goatBoat,context.MkNot(state.cabbageBoat)),
                context.MkAnd(state.farmerBoat, context.MkNot(state.wolfBoat), context.MkNot(state.goatBoat),state.cabbageBoat)
                )

        context.MkAnd(
            (MkXor3 state.farmer state.farmerBoat state.farmerAcross),
            (MkXor3 state.goat state.goatBoat state.goatAcross),
            (MkXor3 state.wolf state.wolfBoat state.wolfAcross),
            (MkXor3 state.cabbage state.cabbageBoat state.cabbageAcross),
            noEating,
            boatCapacity
            )
    
    //Transitions
    let validTransition (state:riverState, state2:riverState) =
        let stationaryFarmer = context.MkAnd(context.MkEq(state.farmer, state2.farmer), context.MkEq(state.farmerBoat, state2.farmerBoat))
        let stationaryWolf = context.MkAnd(context.MkEq(state.wolf, state2.wolf), context.MkEq(state.wolfBoat, state2.wolfBoat))
        let stationaryGoat = context.MkAnd(context.MkEq(state.goat, state2.goat), context.MkEq(state.goatBoat, state2.goatBoat))
        let stationaryCabbage = context.MkAnd(context.MkEq(state.cabbage, state2.cabbage), context.MkEq(state.cabbageBoat, state2.cabbageBoat))
        context.MkOr(
            //+unproductive farmer, simplifies development
            context.MkAnd(stationaryFarmer, stationaryWolf, stationaryGoat, stationaryCabbage),
            //Farmer solo
            context.MkAnd(stationaryGoat, stationaryWolf, stationaryCabbage,
                context.MkOr(
                    context.MkAnd(state.farmer,state2.farmerBoat),
                    context.MkAnd(state.farmerBoat,state2.farmer),
                    context.MkAnd(state.farmerBoat,state2.farmerAcross),
                    context.MkAnd(state.farmerAcross,state2.farmerBoat))),
            //+Wolf
            context.MkAnd(
                stationaryGoat,
                stationaryCabbage,
                context.MkOr(
                    context.MkAnd(state.farmer,state2.farmerBoat,state.wolf,state2.wolfBoat),
                    context.MkAnd(state.farmerBoat,state2.farmer,state.wolfBoat,state2.wolf),
                    context.MkAnd(state.farmerBoat,state2.farmerAcross,state.wolfBoat,state2.wolfAcross),
                    context.MkAnd(state.farmerAcross,state2.farmerBoat,state.wolfAcross,state2.wolfBoat))),
            //+Goat
            context.MkAnd(
                stationaryWolf,
                stationaryCabbage,
                context.MkOr(
                    context.MkAnd(state.farmer,state2.farmerBoat,state.goat,state2.goatBoat),
                    context.MkAnd(state.farmerBoat,state2.farmer,state.goatBoat,state2.goat),
                    context.MkAnd(state.farmerBoat,state2.farmerAcross,state.goatBoat,state2.goatAcross),
                    context.MkAnd(state.farmerAcross,state2.farmerBoat,state.goatAcross,state2.goatBoat))),
            //+Cabbage
            context.MkAnd(
                stationaryWolf,
                stationaryGoat,
                context.MkOr(
                    context.MkAnd(state.farmer,state2.farmerBoat,state.cabbage,state2.cabbageBoat),
                    context.MkAnd(state.farmerBoat,state2.farmer,state.cabbageBoat,state2.cabbage),
                    context.MkAnd(state.farmerBoat,state2.farmerAcross,state.cabbageBoat,state2.cabbageAcross),
                    context.MkAnd(state.farmerAcross,state2.farmerBoat,state.cabbageAcross,state2.cabbageBoat)))
                    )

    //
    let allLeft (state:riverState) =
        context.MkAnd(
            state.farmer,
            state.wolf,
            state.goat,
            state.cabbage
            )

    let allAcross (state:riverState) =
        context.MkAnd(
            state.farmerAcross,
            state.wolfAcross,
            state.goatAcross,
            state.cabbageAcross
            )
    
    //
    let solver = context.MkSolver()

    let trajectories = Array.init 15 (fun i -> makeState i)
    let finalState = trajectories |> Array.last
   
    //
    solver.Assert(allLeft trajectories.[0])
    trajectories |> Array.map isValidState |> (fun states -> solver.Assert(states))
    trajectories |> Array.pairwise |> Array.map validTransition |> (fun states -> solver.Assert(states))
    solver.Assert(finalState |> allAcross)

    let status = solver.Check()

    let printstate step systemState =
        printfn "Step: %i" step

        let truez = context.MkTrue()

        let printWhen name b =
            if solver.Model.Eval(b, true) :?> BoolExpr = truez then
                printf name
            else
                printf "         "
        
        printWhen "Farmer  " systemState.farmer
        printWhen "Farmer  " systemState.farmerBoat
        printWhen "Farmer  " systemState.farmerAcross
        printfn ""

        printWhen "Wolf    " systemState.wolf
        printWhen "Wolf    " systemState.wolfBoat
        printWhen "Wolf    " systemState.wolfAcross
        printfn ""

        printWhen "Goat    " systemState.goat
        printWhen "Goat    " systemState.goatBoat
        printWhen "Goat    " systemState.goatAcross
        printfn ""

        printWhen "Cabbage " systemState.cabbage
        printWhen "Cabbage " systemState.cabbageBoat
        printWhen "Cabbage " systemState.cabbageAcross
        printfn ""
        printfn "-------------------------"

    match status with
    | Status.SATISFIABLE ->
            trajectories |> Array.iteri printstate
    | _ -> printfn "UNSAT"


[<EntryPoint>]
let main argv =

    //petPurchasing()
    
    riverCrossing()
    
    0