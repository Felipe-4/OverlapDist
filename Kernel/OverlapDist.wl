(* ::Package:: *)

(*Needs["maTHEMEatica`"]
SetOptions[EvaluationNotebook[], DefaultNewCellStyle->"Code"];
colors=<|
	"background"->RGBColor["#000000"],
	"fontcolor"->RGBColor["#eeeeee"],
	"primary"->RGBColor["#B87333"],
	"variable"->RGBColor["#55f7df"],
	"module"->RGBColor["#e638e9"],
	"block"->RGBColor["#FFFF00"],
	"error"->RGBColor["#FF0000"],
	"headhighlight"->RGBColor["#02584c"]
|>;
SetColors[colors]
CreateStyleSheet[]
ApplyStyleSheet[]*)


(* ::Section:: *)
(*Package Header*)


BeginPackage["FelipeBarbosa`OverlapDist`"];


CornerPlot::usage="CornerPlot[grid, {x1range, x2range, ...}, {n1\[Sigma]}] creates the corner plot of grid, highlighting the n1\[Sigma] level and assuming the coordinate 
ranges {x1range, x2, range, ...}";
N\[Sigma]GridOverlap::usage="N\[Sigma]GridOverlap[{grid1, grid2,...}, {n1\[Sigma]}]\[LineSeparator]returns the product of probabilities of {grid1, grid2,...} for points inside the \!\(\*
StyleBox[\"n1\[Sigma]\", \"TI\"]\) intersecting region and 0 for points outside";
N\[Sigma]Grid::usage = "N\[Sigma]Grid[grid, {n1\[Sigma]}]\[LineSeparator]replaces numbers in grid outside the \!\(\*
StyleBox[\"n1\[Sigma]\", \"TI\"]\) region by 0.";
ThresholdP;


Begin["`Private`"];


(* ::Section:: *)
(*Definitions*)


MarginalGrid::seq = "The length of `1` can not be bigger than the array depth of the grid";

MarginalGrid[grid_, {i__Integer}]/;(
	ArrayQ[grid] && ArrayDepth[grid]>Length[{i}] && And@@(Positive/@{i})
) := Module[
	{gridDimensions = Range[ArrayDepth@grid], coors = Length[{i}], list},
	
	(*
	Transpose works in a non-intuitive way, but flatten does the simple thing:
	https://mathematica.stackexchange.com/questions/119/flatten-command-matrix-as-second-argument/14810#14810
	*)
	
	list = Join[{i}, Complement[gridDimensions, {i}]]; (*Makes sure "i" comes first*)
	list = Partition[list, 1]; (*for Flatten sintax*)
	
	Total[
		Flatten[grid, list],
		{coors+1, -1}
	]
]

MarginalGrid[grid_, {i__Integer}]/;(
	ArrayQ[grid]&& ArrayDepth[grid] == Length[{i}] && And@@(Positive/@{i})
) := Flatten[grid, Partition[{i},1]]


MarginalGrid[grid_, {i__Integer}]/;(
	ArrayQ[grid]&& ArrayDepth[grid] < Length[{i}] && And@@(Positive/@{i})
):= Message[MarginalGrid::seq, {i}]

MarginalGrid[x___] := Throw[$Failed, failTag[MarginalGrid]]


ThresholdP[grid_,  {prob__}]/; (
	 ArrayQ[grid, _, NumberQ] && And@@(0<=#<=1&/@{prob})
) := Module[
    {throwEmpty, iThresholdValues, getprobPosition, iGrid, positionList, tempvar},
    
    
    throwEmpty[x_List]/; x==={} := Throw["stop"];
    
    iThresholdValues = Sort[{prob}*Total[Flatten@grid]];
    
    getprobPosition[i_, x_]/; x >= First@iThresholdValues := (
        iThresholdValues = Drop[iThresholdValues, 1]; 
        Sow[i]; 
        throwEmpty[iThresholdValues]);
    
    
    iGrid = ReverseSort[Flatten@grid];
    
    tempvar=0.;
    positionList = Reap@Catch@Do[
        getprobPosition[i, tempvar += iGrid[[i]]],
        {i, 1, Length@iGrid}
    
    ]//Last//Last;
    
    positionList = Part[iGrid, positionList];
    
    {
        iGrid[[1]], 
        positionList
    }
]

ThresholdP[x___] := Throw[$Failed, failTag[ThresholdP]]


XLowerUpper[grid_, {pthreshold__}]/;(
	MatrixQ[grid, NumberQ] && And@@(NonNegative/@{pthreshold})
) := Module[
	{igrid, PositiveProbpositions,coords, PositiveProbcoords, length = Length@grid, numberOf\[Sigma] = Length@{pthreshold}, findSmallPositions},
	
	coords = grid[[All,1]];
	igrid = ((grid[[All,2]] - #)&/@{pthreshold})//ArrayReshape[#, {numberOf\[Sigma], length}]&;
	
	PositiveProbpositions = Position[#, x_/;x>=0]&/@igrid;
	
	PositiveProbcoords = Extract[coords, #]&/@PositiveProbpositions;
	
	MinMax/@PositiveProbcoords
]


HDIConfidenceInterval[grid_,  {pmax_, {pthreshold__}}]/;(
	MatrixQ[grid, NumberQ] (*&& And@@(NonNegative/@{pmax, pthreshold})*)
) := Module[
	{int, xmax, xlowerbound, xupperbound, \[Delta]lower, \[Delta]upper, igrid, small, smallPositions},
	(*Just find it in the grid, because NSolve is finding just one value *)
	
	
	{xlowerbound, xupperbound} = Transpose@XLowerUpper[grid, {pthreshold}];
	
	xmax = FirstPosition[grid[[All,2]], pmax]//Last;
	xmax = grid[[xmax, 1]];
	
	{\[Delta]lower, \[Delta]upper} = {xmax-xlowerbound, xupperbound-xmax};
	
	MapThread[
		Around[xmax, {#1, #2}]&,
		{\[Delta]lower, \[Delta]upper}
	]
]

XLowerUpper[x___] := Throw[$Failed, failTag[XLowerUpper]]
HDIConfidenceInterval[x___] := Throw[$Failed, failTag[HDIConfidenceInterval]]


MakeContourPlotGrid[grid_, {coords__List}]/;(
	VectorQ[grid, NumberQ] && Length@grid == Times@@(Length/@{coords})
) := Module[
	{ gridCoords, dim = Length@{coords} , flatten, gridLength = Length@grid},
	
	flatten[0] := 1;
	flatten[dim-1]/;dim>1 := dim-1;
	
	gridCoords = Outer[
		List,
	coords
	]//Flatten[#, flatten[dim-1]]&;
	
	Riffle[gridCoords, grid]//ArrayReshape[#, {gridLength, dim+1}]&
]

MakeContourPlotGrid[x___] := Throw[$Failed, failTag[MakeContourPlotGrid]]


Options[PersonalizedListContourPlot] = Module[

	{list, colorList},
	
	list = (Options@ListContourPlot)/.{
		(Contours->x_) -> Nothing,
		(PerformanceGoal->z_) -> (PerformanceGoal->"Quality"), 
		(InterpolationOrder->x_) -> (InterpolationOrder->2),
		(Background->x_) -> (Background->White),
		(Frame->x_) -> (Frame->True),
		(PlotRange ->x_) -> Nothing
	}
];


PersonalizedListContourPlot[grid_, {pmax_, {contours__}}, {colors__}, {plotRangex_, plotRangey_}, OptionsPattern[]] := Module[
	{colorList,contourList, optsListContourPlot, minThreshold},
	
	minThreshold = Sort[{contours}][[1]];
	
	colorList = With[
		{list = {colors}},
		If[Length@{contours} > Length[list], Join[list, ConstantArray[Black, Length@{contours}]], list]
	];
	
	colorList = colorList[[1;;Length@{contours}]];
		
	contourList = MapThread[
		List[#1, Directive[#2]]&,
		{{contours}, colorList}
	];
	
	optsListContourPlot = (#1 -> OptionValue[PersonalizedListContourPlot, #1])&@@@Options[PersonalizedListContourPlot];
	
	ListContourPlot[
		grid,
		Contours -> contourList,
		PlotRange -> {plotRangex, plotRangey, {0.9 minThreshold, 1.1 pmax}},
		optsListContourPlot
	]
]

AllContourPlots[x___] := Throw[$Failed, failTag[AllContourPlots]]


Options[PersonalizedListLinePlot] = Module[{list, colorList},

	list = (Options@ListLinePlot)/.{
		(Background-> x_ )-> (Background->White),(Frame->x_)-> (Frame->True), 
		(GridLines->x_) -> Nothing, 
		(GridLinesStyle->x_) -> (GridLinesStyle->Directive[Black, Dashed, Thickness[0.003]]),
		(PlotLegends -> x_) -> Nothing,
		(FrameTicks->x_) -> Nothing,
		(PlotRange -> x_) -> Nothing
	}
];


PersonalizedListLinePlot[grid_, {CI__Around}, {colors__}, gridL_?BooleanQ, plotRangex_, OptionsPattern[]]/;(
	MatrixQ[grid, NumberQ] 
) := Module[
	{framelabel, lastCoord = Length@grid, gridLines, legends, \[Delta]Lower, \[Delta]upper,optValues, xLower, xupper, colorList, optsListLinePlot, labels},
	
	
	
	\[Delta]Lower = {CI}[[All, 2,1]]; \[Delta]upper = {CI}[[All,2,2]];
	
	xLower = {CI}[[1,1]] -\[Delta]Lower; xupper = {CI}[[1,1]] + \[Delta]upper; 
	
	(*PassColors:*)
	colorList = With[
		{list = {colors}},
		If[Length[xLower] > Length[list], Join[list, ConstantArray[Black, Length@xLower]], list]
		];
		
	colorList = colorList[[1;;Length@xLower]]; 
	
	xLower = MapThread[
		{#1, Directive[#2,Dashed,  Thickness[0.003]]}&,
		{xLower,colorList}	
	];
	
	xupper = MapThread[
		{#1, Directive[#2,Dashed,  Thickness[0.003]]}&,
		{xupper,colorList}	
	];
	
	gridLines = If[gridL,  Join[xLower, xupper], None];
	
	labels = Placed[#, {Left, Top}]&/@{CI};
		
	
	(*Get Options*)
	optsListLinePlot = (#1 -> OptionValue[PersonalizedListLinePlot, #1])&@@@Options[PersonalizedListLinePlot];
	
	
		ListLinePlot[
			grid,
			GridLines -> {gridLines, None},
			PlotLegends -> None(*labels*),
			FrameTicks -> {Automatic,None},
			PlotRange -> {plotRangex, All},
			optsListLinePlot
		]
	
]


CornerPlot::fail="The function failed. The failure occured in function `1` ";


Options[CornerPlot] = Module[
	{colorlist,oneDopts, twoDopts, plotGrid},
	
	oneDopts = Options[PersonalizedListLinePlot];
	twoDopts = Options[PersonalizedListContourPlot];
	plotGrid = Options[ResourceFunction["PlotGrid"]];
	colorlist = {RGBColor[0., 0., 0.],RGBColor[0, 0, 1],RGBColor[0, 1, 0],RGBColor[1, 0, 0],RGBColor[1, 0.5, 0],RGBColor[1, 1, 0],RGBColor[0.00784313725490196, 0.5098039215686274, 0.9294117647058824],RGBColor[0.996078431372549, 0.3607843137254902, 0.027450980392156862`],RGBColor[0.5411764705882353, 0.7137254901960784, 0.027450980392156862`],RGBColor[0.1450980392156863, 0.43529411764705883`, 0.3843137254901961],RGBColor[0.15294117647058825`, 0.11372549019607843`, 0.49019607843137253`],RGBColor[0.47058823529411764`, 0.2627450980392157, 0.5843137254901961],RGBColor[0.8901960784313725, 0.011764705882352941`, 0.49019607843137253`],RGBColor[0.9058823529411765, 0.027450980392156862`, 0.12941176470588237`]};
	
	{
		"n\[Sigma]Colors" -> colorlist,
		"GridLines" -> True,
		"PlotRange" -> {All},
		"ListLinePlot" -> oneDopts, 
		"ListContourPlot" -> twoDopts,
		"PlotGrid" -> plotGrid
	}
];


CornerPlot::InvalidPlotRange = "Invalid PlotRange list, elements can be either \"{a,b}\" with b>a or \"All\".
The list length should be smaller or equal to the number of coordinates";


testRange[x_List]/; Length@x==2 && Less@@x := True
testRange[All] := True

TestPlotRange[plotrangeList_, dim_]/; 1<= Length[plotrangeList] <=dim := If[
	And@@(testRange/@plotrangeList), 
	True, 
	Throw[Message[CornerPlot::InvalidPlotRange]]
]

testRange[x___] := Throw[Message[CornerPlot::InvalidPlotRange]]
TestPlotRange[x___] := Throw[Message[CornerPlot::InvalidPlotRange]]


CornerPlot[grid_List, vars_List, {HDI__}, OptionsPattern[]]/;(
	ArrayQ[grid,_, NumberQ] && MatrixQ@vars && And@@(0<#<=1&/@{HDI})
) := Module[
	{CoordinateValues, dim =Length@vars, matrixGrid, hdrs, confidenceIntervals, f, plot, arguments, n\[Sigma]s,
	marginal, frameLabel, \[CapitalDelta]x, passArguments, arrayDimensions, plotRange
	},
	
	(*Set the correct frame labels for the TrianglePlot*)
	frameLabel[x_]/; UnsameQ[x,dim] := {None, None}; frameLabel[dim] := {ToString[vars[[-1,1]]], None};
	frameLabel[dim, j_]/;j>1 := {ToString[vars[[j,1]]], None};
	frameLabel[i_, 1]/; i<dim := {None, ToString[vars[[i,1]]]};
	frameLabel[dim,1] := ToString/@{ vars[[1,1]], vars[[dim, 1]] };
	frameLabel[i_, j_] := {None,None};
	
	(*Define coordinteValues:*)
	arrayDimensions = Dimensions@grid;
	(CoordinateValues[#] = Subdivide[Sequence@@vars[[#, 2;;3]], -1 + arrayDimensions[[#]]] )&/@Range[dim];
	
	(CoordinateValues[#] = Flatten@CoordinateValues[#])&/@Range[dim];
		
	
	Catch[
		(*Let's see the plot range:*)
		TestPlotRange[OptionValue[CornerPlot, "PlotRange"], dim];
		Evaluate@(plotRange/@Range[dim]) = Join[OptionValue["PlotRange"], All&/@Range[dim] ]//Take[#, dim]&;
		
		
		
		(*Get all marginalizations:*)
		
		Do[(*Make "j" the "x" coordinate, so that plots in the same column will share the x axis in the final grid*)
			marginal[i,j] = Flatten@Transpose@MarginalGrid[grid, {i,j}], 
			{i, 2, dim}, 
			{j,1, i-1}
		];
		
		(marginal[#] = MarginalGrid[grid, {#}])&/@Range[dim];
		
		
		(*Calulate threshold probabilities*)
		(n\[Sigma]s[#] = ThresholdP[marginal[#], {HDI}])&/@Range[dim];
		
		Do[
			n\[Sigma]s[i,j] = ThresholdP[marginal[i,j], {HDI}],
			{i,2,dim}, 
			{j,1,i-1}
		];
		
		
		(*get Grid forms adequate for ContourPlot, ListLinePlot and HDIinterval:*)
		Do[ 
			marginal[i,j] = MakeContourPlotGrid[marginal[i,j], {CoordinateValues[j], CoordinateValues[i]}],
			{i,2,dim}, {j,1,i-1}
		]; 
		
		
		(marginal[#] = MakeContourPlotGrid[marginal[#], {CoordinateValues[#]}])&/@Range[dim];
		
		(*GetHDIintervals:*)
		(\[CapitalDelta]x[#] = HDIConfidenceInterval[marginal[#], n\[Sigma]s[#]])&/@Range[dim];
		
		(plot[#] = PersonalizedListLinePlot[
			marginal[#], 
			\[CapitalDelta]x[#],
			OptionValue[CornerPlot, "n\[Sigma]Colors"],
			OptionValue[CornerPlot, "GridLines"],
			plotRange[#],
			FrameLabel-> frameLabel[#],
			Sequence@@OptionValue[CornerPlot, "ListLinePlot"]
			])&/@Range[dim];
			
		Do[
			plot[i,j]  = PersonalizedListContourPlot[
				marginal[i,j], 
				n\[Sigma]s[i,j],
				OptionValue[CornerPlot, "n\[Sigma]Colors"],
				{plotRange[j], plotRange[i]},
				FrameLabel ->frameLabel[i,j], 
				Sequence@@OptionValue[CornerPlot, "ListContourPlot"]
			],
			{i,2, dim},
			{j,1,i-1}
		];
		passArguments[i_,j_]/; i>j :=plot[i,j]; 
		passArguments[i_,j_]/; j>i := Null;
		passArguments[i_,j_]/; j==i := plot[i];
		
		
		arguments = Table[passArguments[i,j], {i,1,dim}, {j,1,dim}];
		
		ResourceFunction["PlotGrid"][arguments, Sequence@@(OptionValue[CornerPlot, "PlotGrid"])],
		
		_failTag, (Message[CornerPlot::fail, Style[First@#2,Red]];#1)&
	]
]


(*Coords stands for: (lowerLimit, upperLimit, how many points)*)
N\[Sigma]Grid[grid_List,  {N\[Sigma]__}]/;(
	And@@(NonNegative/@{N\[Sigma]}) && ArrayQ[grid, _, NumberQ]

) := Module[
	{thresholdProbs, len = Length@{N\[Sigma]}, res},
	
	thresholdProbs = ThresholdP[grid, {N\[Sigma]}][[2]];
	(*Threshold function keeps onl x>\[Delta] I want x >= \[Delta], so I will diminish just a little bit the values:*)
	thresholdProbs = ((1.- 10.^-10.) #)&/@thresholdProbs;
	
	res = Threshold[grid, #]&/@thresholdProbs;
	
	If[len===1, res[[1]], res]
]


<<Developer`
(*I could make this into compiled function, but it seems fast enough*)
N\[Sigma]GridOverlap[{grids__}, {N\[Sigma]__}]/;( 
	(*pvalues need to be only a sequence of Full arrays with the same dimension.*)
	And@@(Equal@@(Dimensions/@{grids}))
) := Module[

	{igrids, l = Length@{N\[Sigma]}, sigmas = Sort@{N\[Sigma]}, res},
	
	igrids = ToPackedArray/@(N/@{grids});
	
	res = Table[
		
		Times@@((N\[Sigma]Region[#, {sigmas[[i]]}][[1]])&/@igrids),
		
		{i,1, l}
	];
	
	If[l==1, res[[1]], res]
]


(* ::Section::Closed:: *)
(*Package Footer*)


End[];
EndPackage[];
