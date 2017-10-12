open Microsoft.Z3

let petPurchasing() =
    use context = new Microsoft.Z3.Context()

    let dogCount = context.MkIntConst("dog")
    let catCount = context.MkIntConst("cat")
    let mouseCount = context.MkIntConst("mouse")

    //Expression for cost for the animals
    let dogsCost = context.MkMul(context.MkInt(1500), dogCount)
    let catsCost = context.MkMul(context.MkInt(100), catCount)
    let miceCost = context.MkMul(context.MkInt(25), mouseCount)

    let solver = context.MkSolver()
    //Ensure >= number of animals
    solver.Assert(context.MkGe(dogCount,context.MkInt(1)))
    solver.Assert(context.MkGe(catCount,context.MkInt(1)))
    solver.Assert(context.MkGe(mouseCount,context.MkInt(1)))
    
    let summedCost = context.MkAdd(dogsCost, catsCost, miceCost)

    //Ensure we spend exactly all our money
    solver.Assert(context.MkEq(context.MkInt(10000), summedCost))

    let status = solver.Check()

    match status with
    | Status.SATISFIABLE ->
            printfn "dogs: %s, cats: %s, mice: %s"
                (solver.Model.Eval(dogCount, true).ToString())
                (solver.Model.Eval(catCount, true).ToString())
                (solver.Model.Eval(mouseCount, true).ToString())
    | _ -> printfn "UNSAT" 

type riverState = {
    farmerShore:BoolExpr
    farmerBoat:BoolExpr
    farmerAcross:BoolExpr
    wolfShore:BoolExpr
    wolfBoat:BoolExpr
    wolfAcross:BoolExpr
    goatShore:BoolExpr
    goatBoat:BoolExpr
    goatAcross:BoolExpr
    cabbageShore:BoolExpr
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

    //State of the system, true or false for farmer, wolf, goat, cabbage being on shore, boat, across
    //They need to be uniquely named hence the suffix
    let makeState i =
        {
            farmerShore = context.MkBoolConst(i.ToString() + "_1");
            farmerBoat = context.MkBoolConst(i.ToString() + "_2");
            farmerAcross = context.MkBoolConst(i.ToString() + "_3");
            wolfShore = context.MkBoolConst(i.ToString() + "_4");
            wolfBoat = context.MkBoolConst(i.ToString() + "_5");
            wolfAcross = context.MkBoolConst(i.ToString() + "_6");
            goatShore = context.MkBoolConst(i.ToString() + "_7");
            goatBoat = context.MkBoolConst(i.ToString() + "_8");
            goatAcross = context.MkBoolConst(i.ToString() + "_9");
            cabbageShore = context.MkBoolConst(i.ToString() + "_10");
            cabbageBoat = context.MkBoolConst(i.ToString() + "_11");
            cabbageAcross = context.MkBoolConst(i.ToString() + "_12");
            }


    let isValidState (state:riverState) =

        //Describe invalid states as negation
        let noEating =
            context.MkNot(
                context.MkOr(
                    context.MkAnd(context.MkNot(state.farmerShore), state.wolfShore, state.goatShore), //Snack time!
                    context.MkAnd(context.MkNot(state.farmerBoat), state.wolfBoat, state.goatBoat),
                    context.MkAnd(context.MkNot(state.farmerAcross), state.wolfAcross, state.goatAcross),
                    context.MkAnd(context.MkNot(state.farmerShore), state.goatShore, state.cabbageShore),
                    context.MkAnd(context.MkNot(state.farmerBoat), state.goatBoat, state.cabbageBoat),
                    context.MkAnd(context.MkNot(state.farmerAcross), state.goatAcross, state.cabbageAcross)
                    )
                )
        
        //Restrict invalid state of everyone getting in boat as negation
        let boatCapacityRespected =
            context.MkOr(
                context.MkAnd(context.MkNot(state.farmerBoat), context.MkNot(state.wolfBoat), context.MkNot(state.goatBoat), context.MkNot(state.cabbageBoat)),
                context.MkAnd(state.farmerBoat, context.MkNot(state.wolfBoat), context.MkNot(state.goatBoat), context.MkNot(state.cabbageBoat)),
                context.MkAnd(state.farmerBoat, state.wolfBoat, context.MkNot(state.goatBoat), context.MkNot(state.cabbageBoat)),
                context.MkAnd(state.farmerBoat, context.MkNot(state.wolfBoat), state.goatBoat,context.MkNot(state.cabbageBoat)),
                context.MkAnd(state.farmerBoat, context.MkNot(state.wolfBoat), context.MkNot(state.goatBoat),state.cabbageBoat)
                )
        
        //Each entity can strictly only be on shore, in boat, or across (no cloning)
        let onePlaceAtATime =
            context.MkAnd(
                (MkXor3 state.farmerShore state.farmerBoat state.farmerAcross),
                (MkXor3 state.goatShore state.goatBoat state.goatAcross),
                (MkXor3 state.wolfShore state.wolfBoat state.wolfAcross),
                (MkXor3 state.cabbageShore state.cabbageBoat state.cabbageAcross)
            )
        
        context.MkAnd(
            noEating,
            boatCapacityRespected,
            onePlaceAtATime
            )
    
    //Transitions
    let validTransition (state:riverState, state2:riverState) =
        //Helpers, useful to describe others as stationary
        let stationaryFarmer = context.MkAnd(context.MkEq(state.farmerShore, state2.farmerShore), context.MkEq(state.farmerBoat, state2.farmerBoat))
        let stationaryWolf = context.MkAnd(context.MkEq(state.wolfShore, state2.wolfShore), context.MkEq(state.wolfBoat, state2.wolfBoat))
        let stationaryGoat = context.MkAnd(context.MkEq(state.goatShore, state2.goatShore), context.MkEq(state.goatBoat, state2.goatBoat))
        let stationaryCabbage = context.MkAnd(context.MkEq(state.cabbageShore, state2.cabbageShore), context.MkEq(state.cabbageBoat, state2.cabbageBoat))
        //Could factor out more of the movement here if desired
        context.MkOr(
            //+unproductive farmer with no movement, simplifies development
            context.MkAnd(stationaryFarmer, stationaryWolf, stationaryGoat, stationaryCabbage),
            //Farmer solo
            context.MkAnd(stationaryGoat, stationaryWolf, stationaryCabbage,
                context.MkOr(
                    context.MkAnd(state.farmerShore,state2.farmerBoat),
                    context.MkAnd(state.farmerBoat,state2.farmerShore),
                    context.MkAnd(state.farmerBoat,state2.farmerAcross),
                    context.MkAnd(state.farmerAcross,state2.farmerBoat))),
            //+Wolf
            context.MkAnd(
                stationaryGoat,
                stationaryCabbage,
                context.MkOr(
                    context.MkAnd(state.farmerShore,state2.farmerBoat,state.wolfShore,state2.wolfBoat),
                    context.MkAnd(state.farmerBoat,state2.farmerShore,state.wolfBoat,state2.wolfShore),
                    context.MkAnd(state.farmerBoat,state2.farmerAcross,state.wolfBoat,state2.wolfAcross),
                    context.MkAnd(state.farmerAcross,state2.farmerBoat,state.wolfAcross,state2.wolfBoat))),
            //+Goat
            context.MkAnd(
                stationaryWolf,
                stationaryCabbage,
                context.MkOr(
                    context.MkAnd(state.farmerShore,state2.farmerBoat,state.goatShore,state2.goatBoat),
                    context.MkAnd(state.farmerBoat,state2.farmerShore,state.goatBoat,state2.goatShore),
                    context.MkAnd(state.farmerBoat,state2.farmerAcross,state.goatBoat,state2.goatAcross),
                    context.MkAnd(state.farmerAcross,state2.farmerBoat,state.goatAcross,state2.goatBoat))),
            //+Cabbage
            context.MkAnd(
                stationaryWolf,
                stationaryGoat,
                context.MkOr(
                    context.MkAnd(state.farmerShore,state2.farmerBoat,state.cabbageShore,state2.cabbageBoat),
                    context.MkAnd(state.farmerBoat,state2.farmerShore,state.cabbageBoat,state2.cabbageShore),
                    context.MkAnd(state.farmerBoat,state2.farmerAcross,state.cabbageBoat,state2.cabbageAcross),
                    context.MkAnd(state.farmerAcross,state2.farmerBoat,state.cabbageAcross,state2.cabbageBoat)))
                    )

    //Start
    let allLeft (state:riverState) =
        context.MkAnd(
            state.farmerShore,
            state.wolfShore,
            state.goatShore,
            state.cabbageShore
            )
    
    //Success!
    let allAcross (state:riverState) =
        context.MkAnd(
            state.farmerAcross,
            state.wolfAcross,
            state.goatAcross,
            state.cabbageAcross
            )
    
    //
    let solver = context.MkSolver()

    //15 is the magic number, try less and more. (we could also search for this)
    let trajectories = Array.init 15 (fun i -> makeState i)
    let finalState = trajectories |> Array.last
   
    //Assert the trajectories in turn. Each must be a valid state
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
        
        printWhen "Farmer  " systemState.farmerShore
        printWhen "Farmer  " systemState.farmerBoat
        printWhen "Farmer  " systemState.farmerAcross
        printfn ""

        printWhen "Wolf    " systemState.wolfShore
        printWhen "Wolf    " systemState.wolfBoat
        printWhen "Wolf    " systemState.wolfAcross
        printfn ""

        printWhen "Goat    " systemState.goatShore
        printWhen "Goat    " systemState.goatBoat
        printWhen "Goat    " systemState.goatAcross
        printfn ""

        printWhen "Cabbage " systemState.cabbageShore
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