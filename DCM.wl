(* ::Package:: *)

(* ::Chapter:: *)
(*Begin of package*)


BeginPackage["DCM`"]
Unprotect["DCM`*"];
ClearAll["DCM`*"];
ClearAll["DCM`Private`*"];


(* ::Chapter:: *)
(*Usage Messages*)


heavyTailDist::usage = "heavyTailDist[a, r] returns a discrete probability \
distribution on integers with mean r and right tail of the order 1/x^a"

findMaxDegree::usage = "findMaxDegree[pdf, n, p] returns the approximate max degree of \
a graph with n vertices whose degree sequence has limit distribution pdf \
with cutoff probability p"

pdf2Deg::usage = "pdf2Deg[pdf, n] creates a bi-degree sequence \
according to the limit bi-degree distribution pdf\n\
pdf2Deg[pdf, r, n, p] creates a bi-degree sequence for a graph with out-degree fixed \
to be r and in-degrees have distribution pdf and cutoff probability p for maximum degree"

deg2Stub::usage = "de2Stub[deg] turns a degree sequence into a stub (half-edge) sequence"

makeDCM::usage = "makeDCM[deglist] create a random directed model with \
bi-degree sequences indeg, outdeg\n\
makeDCM[n, heads, tails] create a random directed model with \
stub-list heads and tails"

transitProbM::usage = "transitProbM[g] computes the transition probability matrix of g"

stationaryProbEigen::usage = "stationaryProbEigen[g] computes the stationary \
probability distribution for a simple random walk on g \
by using Eigenvectors"

stationaryProbNull::usage = "stationaryProbNull[g] computes the stationary \
probability distribution for a simple random walk on g \
by using NullSpace"

stationaryProb::usage = "stationaryProb[g] computes the stationary \
probability distribution for a simple random walk on g \
by using StationaryDistribution"

stationaryProbSim::usage = "stationaryProbSim[g] computes one stationary \
probability distribution for a simple random walk on g \
by simulating the random walk"

pageRank::usage = "pageRank[g, a] computes the PageRank vector of g \
with teleporting probability a by using Eigenvectors"

pageRankSim::usage = "pageRankSim[g, a] computes the PageRank vector of g \
with teleporting probability a by simulating the PageRank surfer"

isAttractive::usage = "isAttractive[g, v] checks if there is a path from every \
vertex to v in g"

maxStationary::usage = "maxStationary[g, a] returns {pimax, piDelta, prmax, prDelta, attractive} 
where 
* pimax is the maximum stationary value,
* piDelta is the the stationary value of the node with maximum in-degree Delta,
* prmax is the maximum stationary PageRank,
* prDelta is the PageRank of the node with maximum in-degree Delta,
* attractive is if the graph has an attractive component"

maxPageRank::usage = "maxPageRank[g, a] returns {prmax, prDelta, attractive} 
where 
* prmax is the maximum stationary value,
* prDelta is the the stationary value of the node with maximum in-degree Delta,
* attractive is if the graph has an attractive component"

simDCM::usage = "simDCM[pdf, r, n, p, a, nsample] simulates nsample DCM with in-degree distribution \
pdf, out-degree r, size n, with max degree cutoff probability p and \
output the stationary values and PageRank with teleporting probability a"

simAnalyze::usage = "simAnalyze[dt] analyze a Dataset dt which contains simulation \
result for a particular size of graphs"


(* ::Chapter:: *)
(*Functions*)


Begin["`Private`"]


findMaxDegree[pdf_, n_ /; IntegerQ[n] && n >= 1, p_ /; 1 >= p > 0] :=
    Module[{deg = 1, p0 = 1},
        While[n * p0 >= p,
            deg = deg + 1;
            p0 = pdf[deg];
        ];
        deg
    ]


isAttractive[g_, v_] :=
    Module[{n},
        n = VertexCount[g];
        Length[VertexInComponent[g, v]] == n
    ]


deg2Stub[degs_ /; ArrayQ[degs, 1, IntegerQ]] :=
    Module[{nedges, stubs, m = 0},
        nedges = Total[degs];
        stubs = ConstantArray[0, nedges];
        Table[stubs[[m + 1 ;; m + degs[[i]]]] = i; m = m + degs[[i]], {i, 1, Length[degs]}];
        stubs
    ]


heavyTailDist[a_ /; a > 1, r_ /; r > 0] :=
    Module[{prob1, pdf1, mean1, p, p1, prob2, pdf2},
        prob1 = ProbabilityDistribution[1 / x^(a + 1), {x, r, \[Infinity], 1}, Method -> "Normalize"];
        pdf1[x_] = PDF[prob1, x];
        mean1 = Mean[prob1];
        (* Put some weight on 0 to make the mean exact *)
        p1 = p /. Solve[(1 - p) * mean1 == r, p][[1]];
        pdf2[x_] = Piecewise[{{p1, x == 0}, {(1 - p1) pdf1[x], x >= r}}] // Simplify;
        prob2 = ProbabilityDistribution[pdf2[x], {x, 0, \[Infinity], 1}]
    ]


pdf2Deg[pdf_, n_ /; IntegerQ[n] && n >= 1] :=
    Module[{n1, deglist, t, i, d, nhead, ntail, diff, heads, tails},
        n1 = n;
        deglist = {};
        For[t = 0, True, t++, 
            For[i = 0, i <= t, i++, (* the number of nodes with degree {i, t-i} *)
                d = Ceiling[n * pdf[i, t - i]];
                (* avoid having to many node *)
                If[d > 0,
                    d = Min[d, n1];
                    deglist = deglist ~ Join ~ ConstantArray[{i, t - i}, d];
                    n1 = n1 - d;
                    If[n1 <= 0,
                        Break[]
                    ]
                ]
            ];
            If[n1 <= 0,
                Break[]
            ]
        ];
        {heads, tails} = deglist = (deglist // Transpose);
        {nhead, ntail} = Total[deglist, {2}];
        (* Perturb the degrees to have the same number of heads and tails *)
        diff = Abs[nhead - ntail];
        Which[
            nhead < ntail,
                heads = (heads[[ ;; diff]] + 1) ~ Join ~ (heads[[diff + 1 ;; ]])
            ,
            nhead > ntail,
                tails = (tails[[ ;; diff]] + 1) ~ Join ~ (tails[[diff + 1 ;; ]])
        ];
        {heads, tails}
    ]


pdf2Deg[pdf_, r__ /; IntegerQ[r] && r >= 1, n_ /; IntegerQ[n] && n >= 1, p_ /; 0 < p <= 1] :=
    Module[{maxdeg, nedge, d, dn, deglist},
        maxdeg = findMaxDegree[pdf, n, p];
        (* We only need to construct the in-degree sequence *)
        nedge = r * n;
        deglist = {};
        For[d = maxdeg, d >= 2, d--, 
            dn = Ceiling[n * pdf[d]];
            dn = Min[dn, Floor[nedge / d]];
            deglist = ConstantArray[d, dn] ~ Join ~ deglist;
            nedge -= dn * d
        ];
        (* Add some degree 0 nodes to make the total number of nodes correct *)
        deglist = PadLeft[deglist, n];
        (* Add some half edges make the total number of edges correct *)
        If[nedge > 0,
            deglist[[ ;; nedge]] += 1
        ];
        {deglist, ConstantArray[r, n]}
    ]


makeDCM[deglist_] :=
    Module[{heads, tails},
        {heads, tails} = deg2Stub /@ deglist;
        makeDCM[Length[deglist[[1]]], heads, tails]
    ]


makeDCM[n_Integer, heads_List, tails_List] :=
    Module[{},
        Graph[Range[n], Thread[tails \[DirectedEdge] RandomSample[heads]]]
    ]


transitProbM[g_] :=
    Module[{adj, outdeg, transit},
        adj = AdjacencyMatrix[g];
        outdeg = Total[adj, {2}];
        transit = MapIndexed[(#1 / outdeg[[#2[[1]]]])&, adj] // SparseArray
    ]


stationaryProbEigen[g_] :=
    Module[{transit, pi, n, ev},
        n = VertexCount[g];
        transit = Transpose[transitProbM[g]];
        ev = Eigenvectors[N @ transit, 1, Method -> {"Arnoldi"}][[1]];
        pi = ev / Total[ev]
    ]


stationaryProbNull[g_] :=
    Module[{transit, pi, n, ev},
        n = VertexCount[g];
        transit = Transpose[transitProbM[g]];
        ev = First[N[NullSpace[transit - IdentityMatrix[{n, n}, SparseArray]]]];
        pi = ev / Total[ev]
    ]


stationaryProb[g_] :=
    Module[{n, mp, stationary, pi},
        n = VertexCount[g];
        mp = DiscreteMarkovProcess[1, g];
        stationary = StationaryDistribution[mp];
        pi = NProbability[x == #, x \[Distributed] stationary]& /@ Range[n]
    ]


stationaryProbSim[g_, steps_, a_:0]:=
    Module[{n, mp, walk, giant, pi1, tally, cur, prev, transit},
        n=VertexCount[g];
        pi=ConstantArray[0., n];
        transit=(1-a)*transitProbM[g] + a/n;
        mp=DiscreteMarkovProcess[1, transit];
        walk=RandomFunction[mp, {1, steps}]["Values"];
        tally=SortBy[Tally[walk], First];
        giant=tally[[;;, 1]];
        pi1=tally[[1;;All, 2]]/steps//N;
        prev=1;
        For[i=1, i<=Length[giant], i++,
            cur = giant[[i]];
            For[j=prev+1, j<cur, j++,
                pi[[j]] = 0
                ];
            pi[[cur]] = pi1[[i]];
            prev = cur;
        ];
        pi
    ]


stationaryProbSim[g_]:=
    Module[{n, steps},
        n=VertexCount[g];
        steps=Round[50*n Log[n]];
        stationaryProbSim[g, steps]
    ]


pageRank[g_, a_ /; 0 <= a <= 1] :=
    Module[{transit, pi, n, ev},
        n = VertexCount[g];
        transit = (1 - a) * Transpose[transitProbM[g]] + a / n;
        ev = Eigenvectors[N @ transit, 1, Method -> {"Arnoldi"}][[1]];
        pi = ev / Total[ev]
    ]


pageRankSim[g_, a_/;0<=a<=1, steps_:0]:=
    Module[{n, s},
        n=VertexCount[g];
        If[steps==0, s=Round[50*n Log[n]], s=steps];
        stationaryProbSim[g, s, a]
    ]


maxStationary[g_, a_] :=
    Module[{n, pi, pr, indeglist, vDelta, piDelta, prDelta, vpimax, vprmax, pimax, prmax, attractive},
        n = VertexCount[g];
        (* Find the max in-dgree node *)
        indeglist = VertexInDegree[g];
        vDelta = Ordering[indeglist, -1][[1]];
        (* Comptue the stationary value *)
        pi = stationaryProbEigen[g];
        (* Find the stationary value of the node with max in-degree *)
        piDelta = pi[[vDelta]];
        (* Find the max stationary value *)
        vpimax = Ordering[pi, -1][[1]];
        pimax = pi[[vpimax]];
        attractive = isAttractive[g, vDelta];
        (* Comptue the PageRank *)
        If[a == 0,
            pr = pi
            ,
            pr = pageRank[g, a]
        ];
        (* Find the PageRank of the node with max in-degree *)
        prDelta = pr[[vDelta]];
        (* Find the max PageRank *)
        vprmax = Ordering[pr, -1][[1]];
        prmax = pr[[vprmax]];
        (* is the graph attractive? *)
        attractive = isAttractive[g, vDelta];
        {pimax, piDelta, prmax, prDelta, attractive}
    ]


simDCM[pdf_, r_, n_, p_, a_, nsample_] :=
    Module[{degseq, heads, tails, data, maxdeg, col, m},
        m = n * r;
        degseq = pdf2Deg[pdf, r, n, p];
        maxdeg = Max[degseq[[1]]];
        {heads, tails} = deg2Stub /@ degseq;
        data = ParallelTable[maxStationary[makeDCM[n, heads, tails], a], {i, 1, nsample}];
        (* turn data into a dataset *)
        col = {"pimax", "piDelta", "prmax", "prDelta", "attractive"};
        data = Dataset[data][All, AssociationThread[col, Range[Length[col]]]];
        Dataset[<|"n" -> n, "m" -> m, "maxdeg" -> maxdeg, "data" -> data|>]
    ]


simAnalyze[dt_] :=
    Module[{dt1, dt2, dt3, collist},
        collist = {"pimax", "piDelta", "prmax", "prDelta"};
        dt1 = dt["data"];
        dt2 = dt1[Select[#attractive == True&]][All, collist];
        dt3 = dt[{"n", "m", "maxdeg"}] ~ Join ~ Mean[dt2];
        dt3["\[CapitalDelta]/m"] = (#["maxdeg"] / #["m"])& @ dt // Normal // N;
        With[{col = #},
            (dt3[ToString[StringForm["``/(\[CapitalDelta]/m)", col]]] = (#[col] / #["\[CapitalDelta]/m"])& @ dt3 // Normal // N)
        ]& /@ collist;
        dt3
    ]


End[]
Protect["DCM`*"];

EndPackage[]
