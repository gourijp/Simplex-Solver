/**
 * Created by Gouri on 2/4/2016.
 */
var http = require('http');
var url = require('url');

var handleRequest = function(request, response){
    var url_parts = url.parse(request.url, true);
    var query = url_parts.query;

    var simplexValues = solutionSimplex(query.q);
    response.end(JSON.stringify(simplexValues));
}

var server = http.createServer(handleRequest);

server.listen(1228);


var preParserFunction = function(textData){
    var objectOfEquations = {};
    objectOfEquations.arrayOfConstraints = [];
    objectOfEquations.arrayOfPrincipleGoal = [];

    var arrayOfAllEquations = textData.split("\n");
    arrayOfAllEquations.pop();

    for(var i=0; i<arrayOfAllEquations.length; i++){
        arrayOfAllEquations[i] = arrayOfAllEquations[i].split(" ");


        if(arrayOfAllEquations[i][0] === "Eq"){
            objectOfEquations.arrayOfConstraints.push(arrayOfAllEquations[i][1]);
        }

        else if(arrayOfAllEquations[i][0] === "Maximize"){
            objectOfEquations.arrayOfPrincipleGoal.push(arrayOfAllEquations[i][1]);
        }
    }
    return objectOfEquations;
}


var coefficientParser = function(LHSOfEquation){

    var result = {};
    result.coefficients = [];
    result.variables = [];
    while(LHSOfEquation.indexOf("x") !== -1) {
        var indexOfx = LHSOfEquation.indexOf("x");
        var coefficientTerm = LHSOfEquation.substr(0, indexOfx);
        var variableTerm = LHSOfEquation.substr(indexOfx, indexOfx +1);
        var lengthOfTerm = coefficientTerm.length + variableTerm.length;
        result.coefficients.push(parseInt(coefficientTerm));
        result.variables.push(variableTerm);
        LHSOfEquation = LHSOfEquation.replace(LHSOfEquation.substr(0, lengthOfTerm),'');
    }
    return result;
}

var swap = function(arr, indexOne, indexTwo){
    var temp = arr[indexOne];
    arr[indexOne] = arr[indexTwo];
    arr[indexTwo] = temp;
}

var parserFunction = function(objectOfEquations){

    var objectWithEqDetails = {};

    objectWithEqDetails.goal = {};
    objectWithEqDetails.goal.Operation = "=";
    objectWithEqDetails.goal.Constant = parseInt(0);
    objectWithEqDetails.goal.Parts = coefficientParser(objectOfEquations.arrayOfPrincipleGoal[0]);

    objectWithEqDetails.constraintsArr = [];

    for(var i=0; i<objectOfEquations.arrayOfConstraints.length; i++) {

        var tempArray = objectOfEquations.arrayOfConstraints[i].split("<=");
        var tempObject = {};
        tempObject.Operation = "<=";
        tempObject.Constant = parseInt(tempArray[1]);
        tempObject.Parts = coefficientParser(tempArray[0]);
        objectWithEqDetails.constraintsArr.push(tempObject);
    }
    return objectWithEqDetails;
}

var canonicalFormObjectParser = function(objectWithEqDetails){

    var goalCoefficientArray = objectWithEqDetails.goal.Parts.coefficients;

    for(var i=0; i< goalCoefficientArray.length; i++){
        goalCoefficientArray[i] = parseInt((-1)*goalCoefficientArray[i]);
    }

    goalCoefficientArray.unshift(parseInt(1));
    objectWithEqDetails.goal.Parts.variables.unshift("z");


    for(var i=0; i<objectWithEqDetails.constraintsArr.length; i++){
        objectWithEqDetails.constraintsArr[i].Operation = "=";
        objectWithEqDetails.constraintsArr[i].Parts.coefficients.push(parseInt(1));
        objectWithEqDetails.constraintsArr[i].Parts.variables.push("s"+ parseInt(i+1));
    }

    return objectWithEqDetails;
}


var canonicalFormOne = function(objectWithEqDetails){
    var arrayOfArray = [];
    var listOfVariables = [];
    var rowZero = [];

    var goalVariablesArray = objectWithEqDetails.goal.Parts.variables;
    var goalCoefficientsArray = objectWithEqDetails.goal.Parts.coefficients;
    var constraints = objectWithEqDetails.constraintsArr;

    for(var i=0; i<goalVariablesArray.length; i++){
        listOfVariables.push(goalVariablesArray[i]);
        rowZero.push(goalCoefficientsArray[i]);
    }

    for(var i=0; i< constraints.length; i++){
        for(var j=0; j<constraints[i].Parts.variables.length; j++){
            if(listOfVariables.indexOf(constraints[i].Parts.variables[j]) === -1){
                listOfVariables.push(constraints[i].Parts.variables[j]);
            }
        }
    }

    var fillerZeros = listOfVariables.length - rowZero.length;

    for(var i =0; i< fillerZeros; i++){
        rowZero.push(0);
    }

    arrayOfArray[0] = listOfVariables;
    arrayOfArray[1] = rowZero;



    for(var i=0; i< constraints.length; i++) {
        var tempArr = [];

        for (var k = 0; k < listOfVariables.length; k++) {
            tempArr.push(0);
        }

        for (var j = 0; j < constraints[i].Parts.variables.length; j++) {
            var indexInList = listOfVariables.indexOf(constraints[i].Parts.variables[j]);
            tempArr[indexInList] = constraints[i].Parts.coefficients[j];
        }
        arrayOfArray[i+2] = tempArr;
    }

    arrayOfArray[0].push("c");
    arrayOfArray[1].push(objectWithEqDetails.goal.Constant);

    for(var i=0; i< constraints.length; i++){
        arrayOfArray[i+2].push(constraints[i].Constant);
    }

    return arrayOfArray;
}

var isSimplexSolved = function(table){
    var a = table[1].pop();

    var minElementInRowZero = Math.min.apply(Math,table[1]);
    table[1].push(a);

    return minElementInRowZero < 0;
}

var canonicalFormTwo = function(tableOne){

    while(isSimplexSolved(tableOne)) {
        var a = tableOne[1].pop();

        var minElementInRowZero = Math.min.apply(Math,tableOne[1]);
        tableOne[1].push(a);

        var indexOfMinElement = tableOne[1].indexOf(minElementInRowZero);

        var tempIndex = undefined;
        var tempRatio = undefined;

        for(var i=2; i<tableOne.length; i++){
            if(tableOne[i][indexOfMinElement] !== 0){
                var ratio = parseInt(tableOne[i][tableOne[0].length - 1]/tableOne[i][indexOfMinElement]);

                if((tempRatio > ratio)||(tempRatio === undefined)){
                    tempRatio = ratio;
                    tempIndex = i;
                }
            }
        }
        var dividingNumber = tableOne[tempIndex][indexOfMinElement];
        for(var i=0; i<tableOne[tempIndex].length; i++){

            tableOne[tempIndex][i] = tableOne[tempIndex][i]/ dividingNumber;
        }

        for(var i=1; i<tableOne.length; i++) {

            if(i === tempIndex){
                continue;
            }

            var factor = -1 * tableOne[i][indexOfMinElement];
            for(var j=0; j<tableOne[0].length; j++) {
                tableOne[i][j] = tableOne[tempIndex][j]*factor + tableOne[i][j];
            }
        }

    }
    return tableOne;
}


var solutionSimplex = function(Text){
    var objectOfEquations = preParserFunction(Text);
    var objectWithEqDetails = parserFunction(objectOfEquations);
    var canonicalFormDetailsObject = canonicalFormObjectParser(objectWithEqDetails);
    var tableOne = canonicalFormOne(canonicalFormDetailsObject);
    var basicFeasibleSolution = canonicalFormTwo(tableOne);

    var tempObj = {};

    for(var i=1; i<basicFeasibleSolution.length; i++){
        for(var j=0; j<basicFeasibleSolution[0].length; j++){
            if(basicFeasibleSolution[i][j] === 1) {
                tempObj[basicFeasibleSolution[0][j]] = basicFeasibleSolution[i][basicFeasibleSolution[0].length - 1];
                i++;
                if(i === basicFeasibleSolution.length){
                    break;
                }
                j=0;
            }
        }
    }
    return tempObj;
}
