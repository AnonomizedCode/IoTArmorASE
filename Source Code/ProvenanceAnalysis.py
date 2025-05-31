import subprocess
import json
import argparse
import sys
import os 
import random
import stat
import statistics
import model
import math
import datetime
import time
import pickle
from collections import OrderedDict

import time
#import daemon
import signal
from csv import reader

averageProbabilityTotal = 0
averageProbabilityNum = 0
minimumProabilityFactor = 0

allowedTransitions = {}

distribution = []
bucketsTime = []
bucketsContext = []
bw = []

transitionDict = {}
validTargets = {}

historyGroupSize = 10
averageQueryTime = []

unsafeTranslations = {}
eventTranslations = {}
eventPartTracker = []
contextTranslations = {}
durationTracker = {}
unsafeDurationTracker = {}
eventPredictionDict = {}
overallPredicates = {}
predicateList = {}
version = -1
currentStateRecord = []
transitionsInTraining = {}
runtimeStart = None
largestTransitions = {}

######################################## TUTORIAL ################################################################
# This script allows prediction using Helion.
# The input to this script is training file, vocab file, order and scenarios file.
# The output is saved in the results folder which contains a tab separated values for input scenario and predictions.
# You can configure it to select different prediction length, flavors, and models.

# Usage:
# python3 helion_predictions.py ../data/generated_data/validation/scenarios_from_evaluators/ev1-scenarios.txt  ../data/generated_data/training/training_model/helion.train -o 3 -v ../data/generated_data/training/training_model/helion.vocab 

# Simple Usage of brain server:
# 1. Run Helion server with: 
# braind ../data/helion.train.txt ../data/helion.vocab 
# 2. Make request with:
# cat request > /tmp/fifo0 && cat /tmp/fifo1
################################################################################################################

# Directory to save predictions to
OUTPUT_DIR = '../results/'

# NUmber of Predictions
PREDICTION_LENGTH = 10

# Model Algorithm ; alternative is backoff
MODEL = 'interpolate'
# Model Flavors
FLAVORS = ['up']

visitedStates = {}

validPathsForHistory = OrderedDict()
validPathsForHistoryTest = {}

timeData = 0

#max_dict_size = 4000000
max_dict_size = 40000000


def checkStateViolationFromProbabilities(unsafeStateDefinition, unsafeStateSpecifics,CurrentState):

    overallProbability = -1

    for unsafeElement in unsafeStateDefinition[0]:
        if not unsafeElement[0] + ':' + unsafeElement[1] in CurrentState:
            continue
        
        if overallProbability == -1:
            overallProbability = CurrentState[unsafeElement[0] + ':' + unsafeElement[1]]
        else:
            overallProbability *= CurrentState[unsafeElement[0] + ':' + unsafeElement[1]]
    return overallProbability

def getTransitionDict():
    global transitionDict,validTargets
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/allowedTransitions.txt", "rb") as myFile:
        transitionDict = pickle.load(myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/permittedTargets.txt", "rb") as myFile:
        validTargets = pickle.load(myFile)


                
def checkIfUnsafeTime(state,durationTrackerTemp,currentTime):
    global unsafeStates, durationTracker, unsafeDurationTracker
    
    stateSplit = state.split('-')
    #reduceState = stateSplit[0] + '-' + state.split('-')[1]
    reduceState = stateSplit[0]
    dateTimeValue = datetime.time(hour = int(stateSplit[1].split(':')[0]),minute = int(stateSplit[1].split(':')[1]))
    


    if len(unsafeStates[reduceState][1]) == 0:
    #if len(unsafeStates[state.split('-')[0]][1]) == 0:
        return 1
    #for unsafeTimes in unsafeStates[state.split('-')[0]][1]:

    for unsafeTimes in unsafeStates[reduceState][1]:
        if unsafeTimes[0] < unsafeTimes[1]:
            if dateTimeValue >= unsafeTimes[0] and dateTimeValue <= unsafeTimes[1]:
                return 1
        else:
            if dateTimeValue <= unsafeTimes[1] or dateTimeValue >= unsafeTimes[0]:
                return 1
    return 0
    

def relevantHistory(flavor, history, n):
    n = min(len(history) + 1, n) 
    found = 0
    for order in range(n, 0, -1): # Start at the highest order and walk down
      # Update the history by applying the Markov assumption after an...
      history = history[-(order-1):] # ...iteration decrements the order
      prefix = ' '.join(history)
      # Find the highest order that contains a prefix slice...
      if timeData == 1:
        nextTime = str((int(history[-1].split(':')[1].replace('>',''))+1)%60)

      if order != 1 and prefix not in buckets[order-1]:
        # ...the orders that don't contain a prefix slice...
        continue # ...will not factor into the interpolation
      if order == 1:
        continue
      else:
        found = 1
        break
    return found

#Right now only using time for level 0 analysis
def cleanDistribution():
    global bucketsTime
    global unsafeStates,bucketsContext
    unsafeStateProbabilities = {}

    for bucketIndex, bucket in enumerate(bucketsTime):
        if bucketIndex == 0:
            probabilities = {}
            probabilitiesFinal = {}
            probabilitiesTotal = {}
            for token, probability in bucketsTime[0].items():
                
                if token != "<s>" and token != "</s>":
                    #Right now adding all probailities, may eventually want to differentiate some
                    if token.split("-")[0] + ">" in probabilities:
                            probabilities[token.split("-")[0]+ ">"] += 10**probability
                            probabilitiesTotal[token.split("-")[0]+ ">"] += 1
                    else:
                        probabilities[token.split("-")[0] + ">"] = 10**probability
                        probabilitiesTotal[token.split("-")[0]+ ">"] = 1
                else:
                    probabilities[token] = probability
            for token, probability in bucketsTime[0].items():
                if token != "<s>" and token != "</s>":

                    #Right now adding all probailities, may eventually want to differentiate some
                    #print(10**probability)
                    #print(probabilities[token.split("-")[0] + ">"])
                    #print(probabilitiesTotal[token.split("-")[0]+ ">"])
                    #exit()
                    if (10**probability)/(probabilities[token.split("-")[0] + ">"]/probabilitiesTotal[token.split("-")[0]+ ">"]) >= 2:
                        probabilitiesFinal[token] = (10**probability)
                    elif (10**probability)/(probabilities[token.split("-")[0] + ">"]/probabilitiesTotal[token.split("-")[0]+ ">"]) <= 0.5:
                        probabilitiesFinal[token] = (10**probability)
                    # elif token.split(":")[0] + ">" in probabilities:
                        # probabilitiesFinal[token.split(":")[0]+ ">"] += 10**probability
                    # else:
                        # #probabilitiesFinal[token.split(":")[0] + ">"] = 10**probability
                        # probabilitiesFinal[token] = 0
            bucketsTime[0] = probabilitiesFinal
            #print(bucketsTime[0])

    

def getProbabilitiesFromDict(dictEntry, stateInfo, n, time,probabilitiesToUpdate,lineIndex):
    global eventPredictionDict, contextTranslations,largestTransitions,predicateList
    
    thisHistoryHere = []
    historyProbabilities = {}
    # for dictEntryIndex, dictHere in enumerate(eventPredictionDict):
        # if dictHere == "3-soil_temp_1:50":
            # print(eventPredictionDict[dictHere][2])
            # print(eventPredictionDict[dictHere][3])
            # # print(stateInfo)
            # exit()
    notProbabilities = {}
    #for currentHistoryIndex in range(len(stateInfo)):
    # if "17-soil_sensor1_temp:32.0" == dictEntry:
    # for entry in eventPredictionDict[dictEntry][2]:
        # print(entry)
    # print()
    # print()
    # print(dictEntry)
    
    timeStringToAdd = ""
    if len(eventPredictionDict[dictEntry][5]) > 0:
            if time[0] in eventPredictionDict[dictEntry][5]:
                timeStringToAdd += ',Hour:' + time[0]
            else:
                timeStringToAdd += ',Hour:NOT'
    if len(eventPredictionDict[dictEntry][6]) > 0:
            if time[1] in eventPredictionDict[dictEntry][6]:
                timeStringToAdd += ',Minute:' + time[1]
            else:
                timeStringToAdd += ',Minute:NOT'
    if stateInfo["total"] == -1:
        #historyName = {}
        historyName = ""
        for stateElem in stateInfo:
            if stateElem == "total" or stateElem == "otherTotals":
                continue
            stateElemName = stateElem + ':' + stateInfo[stateElem]
            if stateElemName in eventPredictionDict[dictEntry][2]:
                historyName += stateElemName + ","
                #historyName[stateElem.split(':')[0]] = stateElem.split(':')[1]
                #historyName[stateElem.split(':')[0]] = stateElem.split(':')[1]
            else:
                for dictPart in eventPredictionDict[dictEntry][2]:
                    if stateElemName.split(":")[0] == dictPart.split(':')[0]:
                        
                        historyName += stateElemName.split(':')[0] + ":NOT,"
                        #historyName[stateElem.split(':')[0]] = "NOT"
                        break
        # currentElemName = eventPredictionDict[dictEntry][3][0].split(":")[0]
        # currentAdded = 0
        # for dictElem in eventPredictionDict[dictEntry][3][0].split(":")[0]:
            # if currentElemName != dictElem.split(":")[0]:
                
                # if currentAdded == 0:
                    # historyName += currentElemName + ":NOT,"
                # currentElemName = dictElem.split(":")[0]
            # if stateInfo[dictElem] == 1:
                # historyName += dictElem + ","
                # currentAdded = 1
        # if currentAdded == 0:
            # historyName += currentElemName + ":NOT,"
        # historyProbabilities[currentHistory[:-1]+timeStringToAdd] = 1
        if 1==0 and  len(historyName) == 1:
            for historyNamePart in historyName:
                indexID = '<' + str(eventPredictionDict[dictEntry][3].index(historyNamePart + ":" + historyName[historyNamePart] + timeStringToAdd)) + '>'
                historyProbabilities[historyNamePart + ":" + historyName[historyNamePart] + timeStringToAdd] = 1
                #historyProbabilities[historyNamePart + ":" + historyName[historyNamePart] + timeStringToAdd] = 1
        else:
            # historyString = ""
            # for currentHistory in predicateList[dictEntry.split('-')[1]]["predicates"]:
                # for partIndex, historyPart in enumerate(predicateList[dictEntry.split('-')[1]]["predicates"][currentHistory]):
                    # if partIndex !=0:
                        # historyString += ','
                    # historyString += historyPart.split(':')[0] + ":" + historyName[historyPart.split(':')[0] ]
                # break
                
            #indexID = '<' + str(eventPredictionDict[dictEntry][3].index(historyString + timeStringToAdd)) + '>'
            indexID = '<' + str(eventPredictionDict[dictEntry][3].index(historyName[:-1])) + '>'
            historyProbabilities[indexID] = 1
            #historyProbabilities[historyString + timeStringToAdd] = 1
        # if lineIndex == 2 and "19-soil_sensor1_vwc:0.987" == dictEntry:
            # print(historyName)
            # print(historyName[-1])
    elif predicateList[dictEntry.split('-')[1]]["predicates"] == {}:
        notProbabilityCalc = 0
        notNecessary = 0
        for currentHistory in eventPredictionDict[dictEntry][2]:
            indexID = '<' + str(eventPredictionDict[dictEntry][3].index(currentHistory)) + '>'
            if 'NOT' in currentHistory:
                notNecessary = 1
                continue

            if currentHistory in stateInfo:
                historyProbabilities[indexID] = stateInfo[currentHistory]
                #historyProbabilities[currentHistory] = stateInfo[currentHistory]
                notProbabilityCalc += stateInfo[currentHistory]
            else:
                historyProbabilities[indexID] = 0
                #historyProbabilities[currentHistory] = 0
                notProbabilityCalc += 0
            
            
    else:
     #for currentHistory in eventPredictionDict[dictEntry][3]:
     for currentHistory in predicateList[dictEntry.split('-')[1]]["predicates"]:
        indexID = '<' + str(eventPredictionDict[dictEntry][3].index(currentHistory + timeStringToAdd)) + '>'
        historyProbabilities[indexID] = 1
        #historyProbabilities[currentHistory + timeStringToAdd] = 1
        # if not currentHistory in predicateList[dictEntry.split('-')[1]]["predicates"]:
            # continue

        #soil_sensor1_vwc:NOT,soil_moist_1_weather:76.0,soil_temp_2_weather:NOT,solar_radiation_high_weather:0.0,temperature_weather:NOT,temperature_high_weather:NOT,batt_vol:NOT,temperature:106.61

        # if lineIndex == 10 and "19-soil_sensor1_vwc:0.987" == dictEntry:
            # jk = currentHistory.split(',')
            # if jk[0] == "soil_sensor1_vwc:NOT" and jk[1] == "soil_moist_1_weather:76.0" and jk[2] == "soil_temp_2_weather:NOT" and jk[3] == "solar_radiation_high_weather:675.0":
                # if  jk[6] == "batt_vol:NOT" and jk[7] == "temperature:106.61":
                    # if  jk[4] == "temperature_weather:94.0" and jk[5] == "temperature_high_weather:94.0":
                    
        # if not currentHistory in predicateList[dictEntry.split('-')[1]]["predicates"]:
            # print(eventPredictionDict[dictEntry][5])
            # exit()
            # historySplit = currentHistory.split(',')
            # for historyPossible in predicateList[dictEntry.split('-')[1]]["predicates"]:
                # historySplit2 = historyPossible.split(',')
                # if historySplit2[0] == 'soil_temp_1_weather:50' and historySplit2[1] == 'humidity_weather:57' and historySplit2[2] == 'soil_moist_1_weather:27' and historySplit2[3] == 'soil_temp_2_weather:52' and historySplit2[4] == 'soil_temp_4_weather:49':
                    # print(historyPossible)
        for predicatePart in predicateList[dictEntry.split('-')[1]]["predicates"][currentHistory]:
            # if lineIndex == 10 and "19-soil_sensor1_vwc:0.987" == dictEntry:
                # for stateInfoHere in stateInfo:
                    # if stateInfoHere != "total" and stateInfoHere != "otherTotals" and stateInfo[stateInfoHere] > 0:
                            # print(stateInfoHere)
                            # print(stateInfo[stateInfoHere])
                # print(predicateList[dictEntry.split('-')[1]]["notDefinitions"])
                # exit()
                #print(predicateList[dictEntry.split('-')[1]]["notDefinitions"])
                # jk = currentHistory.split(',')
                # if jk[0] == "soil_sensor1_vwc:0.4935" and jk[1] == "soil_moist_1_weather:76.0" and jk[2] == "soil_temp_2_weather:NOT" and jk[3] == "solar_radiation_high_weather:675.0":
                    # if  jk[6] == "batt_vol:NOT" and jk[7] == "temperature:106.61":
                        # if  jk[4] == "temperature_weather:94.0" and jk[5] == "temperature_high_weather:94.0":
                            # print(predicatePart)
                            # if "NOT" in predicatePart:
                                # if  predicatePart.split(':')[0] in predicateList[dictEntry.split('-')[1]]["notDefinitions"]:
                                    
                                    # if predicatePart.split(':')[0] in notProbabilities:
                                        # print(notProbabilities[predicatePart.split(':')[0]])
                                    # else:
                                        # notProbabilityCalc = 0
                                        # for notElement in predicateList[dictEntry.split('-')[1]]["notDefinitions"][predicatePart.split(':')[0]]:
                                            # notProbabilityCalc += stateInfo[notElement]
                                        # print(1- notProbabilityCalc)
                            # else:
                                # print(stateInfo[predicatePart])
            if "NOT" in predicatePart:
                if not predicatePart.split(':')[0] in predicateList[dictEntry.split('-')[1]]["notDefinitions"]:
                    # if lineIndex == 2 and "19-soil_sensor1_vwc:0.987" == dictEntry:
                        # print(predicatePart)
                        # print(predicateList[dictEntry.split('-')[1]]["notDefinitions"])
                        # exit()
                    continue
                if predicatePart.split(':')[0] in notProbabilities:
                    historyProbabilities[indexID] *= notProbabilities[predicatePart.split(':')[0]]
                    #historyProbabilities[currentHistory+timeStringToAdd] *= notProbabilities[predicatePart.split(':')[0]]
                else:
                    notProbabilityCalc = 0
                    for notElement in predicateList[dictEntry.split('-')[1]]["notDefinitions"][predicatePart.split(':')[0]]:
                        notProbabilityCalc += stateInfo[notElement]
                    notProbabilities[predicatePart.split(':')[0]] = 1- notProbabilityCalc
                    historyProbabilities[indexID] *= notProbabilities[predicatePart.split(':')[0]]
                    #historyProbabilities[currentHistory+timeStringToAdd] *= notProbabilities[predicatePart.split(':')[0]]
            else:
                historyProbabilities[indexID] *= stateInfo[predicatePart]
                #historyProbabilities[currentHistory+timeStringToAdd] *= stateInfo[predicatePart]
    
    # if lineIndex == 2 or lineIndex == 10:
        # # if "temperature_weather:94.0" in eventPredictionDict[dictEntry][2]:
            # # print(dictEntry)
            # # print(eventPredictionDict[dictEntry][2])
            # # print()
        
        # #if "17-soil_sensor1_temp:32.0" == dictEntry:
        # if "19-soil_sensor1_vwc:0.987" == dictEntry: #and n == 1:
            
            # # total1 = 0
            # # exit()
            
            
            # # print(stateInfo)
           # # #print(predicateList[dictEntry.split('-')[1]]["predicates"])
            # # #print(len(predicateList[dictEntry.split('-')[1]]["predicates"]))
            # for element in historyProbabilities:
                # # print(element)
                # # print(historyProbabilities[element])
                # # print()
                # if historyProbabilities[element] == 1:
                    # print(element)
                    # print(lineIndex)
                    # print()
                    # #total1 += 1
                # # #print(element)
                # # #print(historyProbabilities[element])
            # # print(total1)
            # # exit()
            # if lineIndex == 10:
             # exit()
            # if total1 != 0:
                # print("Total Here")
                # print(total1)
            # if total1 == 0:
                # for element in historyProbabilities:
                    # if historyProbabilities[element] > 0:
                        # print(element)
                        # print(historyProbabilities[element] )
                # exit()
        # for individualElementsHere in eventPredictionDict[dictEntry][2]:
            # if not individualElementsHere.split(":")[0] in notProbabilities:
                # notProbabilities[individualElementsHere.split(":")[0]] = 1
 
            # notProbabilities[individualElementsHere.split(":")[0]] -= stateInfo[-currentHistoryIndex][individualElementsHere.split(':')[0]][individualElementsHere.split(':')[1]]
        # if historyProbabilities == {}:
            # for stateInfoHere in eventPredictionDict[dictEntry][3]:
                # probabilityTotal = 1
                # # if dictEntry == "3-soil_temp_1:50":
                    # # print(eventPredictionDict[dictHere][2])
                    # # print(stateInfoHere)
                    # #print()
                    # # print(stateInfo)
                    # # exit()
                # for historyElement in stateInfoHere.split(','):
                    # if historyElement.split(':')[0] == "Hour" or historyElement.split(':')[0] == "Minute":
                        # continue
                    # if historyElement.split(':')[1] != "NOT":
                        # probabilityTotal *= stateInfo[-currentHistoryIndex][historyElement.split(':')[0]][historyElement.split(':')[1]]
                    # else:
                        # probabilityTotal *= notProbabilities[historyElement.split(':')[0]]
                # if probabilityTotal > 0:
                    # historyProbabilities[eventPredictionDict[dictEntry][3].index(stateInfoHere)] = probabilityTotal
        # else:
            # historyProbabilitiesTemp = {}
            # for stateInfoHere in eventPredictionDict[dictEntry][3]:
                # probabilityTotal = 1
                # for historyElement in stateInfoHere.split(','):
                    # if historyElement.split(':')[0] == "Hour" or historyElement.split(':')[0] == "Minute":
                        # continue
                    # if historyElement.split(':')[1] != "NOT":
                        # probabilityTotal *= stateInfo[-currentHistoryIndex][historyElement.split(':')[0]][historyElement.split(':')[1]]
                    # else:
                        # probabilityTotal *= notProbabilities[historyElement.split(':')[0]]
                # if probabilityTotal > 0:
                    # for historyHere in historyProbabilities:
                        # historyProbabilitiesTemp[str(eventPredictionDict[dictEntry][3].index(stateInfoHere)) + " " + str(historyHere)] = historyProbabilities[historyHere] * probabilityTotal
            # historyProbabilities = historyProbabilitiesTemp.copy()

    # for historyIndexHere, historyHere in enumerate(stateInfo):
        # stateString = ""
        # #currentStateTracker = contextTranslations[int(historyHere.split('-')[1].replace('>',''))].split(',')
        # currentStateTracker = contextTranslations[int(historyHere.replace('>','').replace('<',''))].split(',')
        # for indexCount, deviceIndex in enumerate(eventPredictionDict[dictEntry][1]):
            # if indexCount != 0:
                # stateString += ','
                
            # #currentStateTracker.append(stateInfo[int(deviceIndex)])
            # #print(deviceIndex)
            # #print(eventPredictionDict[dictEntry][2])

            # if currentStateTracker[int(deviceIndex)] in eventPredictionDict[dictEntry][2]:
                # #stateString += stateInfo[int(deviceIndex)]
                # stateString += currentStateTracker[int(deviceIndex)]
            # else:
                # #stateString += stateInfo[int(deviceIndex)].split(':')[0] + ':NOT'
                # stateString += currentStateTracker[int(deviceIndex)].split(':')[0] + ':NOT'
    # # for part in eventPredictionDict[dictEntry]:
        # # print(part)
        # # print()
        # if len(eventPredictionDict[dictEntry][5]) > 0:
            # if time[0] in eventPredictionDict[dictEntry][5]:
                # stateString += "," + time[0]
            # else:
                # stateString += ",HourNOT"
        # if len(eventPredictionDict[dictEntry][6]) > 0:
            # if time[1] in eventPredictionDict[dictEntry][6]:
                # stateString += "," + time[1]
            # else:
                # stateString += ",MinuteNOT"

        # thisHistoryHere.append("<" + str(eventPredictionDict[dictEntry][3].index(stateString)) + ">")

    
    
    # history = thisHistoryHere.copy()
    # historyFirst = history.copy()
    # n = min(len(history) + 1, n)
    backoff_weight = 1.0
    #distribution = {}

    selfProbability = 0
    totalProbability = 0
    historyProbabilityStore = {}
    predicateProbabilityStorage = {}

    for order in range(n, 0, -1):   
      if order == 1:
        #for token, probability in eventPredictionDict[dictEntry][-1]["Base"].items():
        for token in eventPredictionDict[dictEntry][-1]["Base"]:
            if ":NOT" in token or not token in probabilitiesToUpdate:
                continue
            probability = eventPredictionDict[dictEntry][-1]["Base"][token]
            if not ',' in token:
                    probabilitiesToUpdate['total'] += backoff_weight * (10**probability)
            else:
                if token.split(',')[0].split(':')[0] + ',' + token.split(',')[1].split(':')[0] in probabilitiesToUpdate["otherTotals"]:
                    probabilitiesToUpdate["otherTotals"][token.split(',')[0].split(':')[0] + ',' + token.split(',')[1].split(':')[0]] += backoff_weight * (10**probability) 
                else:
                    probabilitiesToUpdate["otherTotals"][token.split(',')[1].split(':')[0] + ',' + token.split(',')[0].split(':')[0]] += backoff_weight * (10**probability) 
            probabilitiesToUpdate[token] += backoff_weight * (10**probability)
            # if token != dictEntry.split('-')[1]:
                # selfProbability += backoff_weight * (probability)
            # totalProbability += backoff_weight * (probability)
      else:
        #for prefix in eventPredictionDict[dictEntry][-1][order-1]:
        for prefix in historyProbabilities:
            prefixSplit = prefix.split(' ')
            # for prefixPart in prefixSplit:
                # actualValues = eventPredictionDict[dictEntry][3][int(prefixPart)].split(',')
                # historyProbability = -1
                # for valueHere in actualValues:
                    # if historyProbability == -1:
                        # historyProbability = stateInfo[valueHere]
                    # else:
                        # historyProbability *= stateInfo[valueHere]
                
                
        #historyFirst = historyFirst[-(order-1):] # ...iteration decrements the order
            historyFirst = prefixSplit[-(order-1):] # ...iteration decrements the order
            prefix = ' '.join(historyFirst)

            if prefix not in eventPredictionDict[dictEntry][-1]:
                continue
            
            #for token, probability in eventPredictionDict[dictEntry][-1][order-1][prefix]:
            #for token, probability in eventPredictionDict[dictEntry][-1][prefix]:
            for token in eventPredictionDict[dictEntry][-1][prefix]:
                if ":NOT" in token or not token in probabilitiesToUpdate:
                    continue
                    
                #if not token in predicateProbabilityStorage:
                 #   predicateProbabilityStorage[token] = 0
                probability = eventPredictionDict[dictEntry][-1]["Base"][token]
                if not ',' in token:
                    probabilitiesToUpdate['total'] += backoff_weight * (10**probability) * historyProbabilities[prefix]
                else:
                    if token.split(',')[0].split(':')[0] + ',' + token.split(',')[1].split(':')[0] in probabilitiesToUpdate["otherTotals"]:
                      probabilitiesToUpdate["otherTotals"][token.split(',')[0].split(':')[0] + ',' + token.split(',')[1].split(':')[0]] += backoff_weight * (10**probability) 
                    else:
                      probabilitiesToUpdate["otherTotals"][token.split(',')[1].split(':')[0] + ',' + token.split(',')[0].split(':')[0]] += backoff_weight * (10**probability) 
                probabilitiesToUpdate[token] += backoff_weight * (10**probability) * historyProbabilities[prefix]
                #predicateProbabilityStorage[token] += backoff_weight * (10**probability) * historyProbabilities[prefix]
                #totalProbability += backoff_weight * (10**probability) * historyProbabilities[prefix]
                # if token != dictEntry.split('-')[1]:
                    # selfProbability += backoff_weight * (10**probability) * historyProbabilities[prefix]
                # totalProbability += backoff_weight * (10**probability) * historyProbabilities[prefix]
            # Weights are stored in log space too and we only update them when...
            if prefix in bw:
                backoff_weight *= 1 - ((1-(10 ** bw[prefix]))*historyProbabilities[prefix]) # ...order > 1
            else:
                backoff_weight = backoff_weight
    # selfProbability = selfProbability/totalProbability
    # transitionProbability = (totalProbability-selfProbability)/totalProbability
    # totalProbability = 0
    #transitionProbability = 0

    # for order in range(n, 0, -1):   
      # if order == 1:
        
        # for token, probability in eventPredictionDict[dictEntry][0][0].items():

            # if token != "self":
                # transitionProbability += backoff_weight * (probability)

            # totalProbability += backoff_weight * (probability)
      # else:
      
        # history = history[-(order-1):] # ...iteration decrements the order
        # prefix = ' '.join(history)

        # if prefix not in eventPredictionDict[dictEntry][0][order-1]:
            # continue

        # for token, probability in eventPredictionDict[dictEntry][0][order-1][prefix]:

            # if token != "self":
                # transitionProbability += backoff_weight * (10**probability)
            # totalProbability += backoff_weight * (10**probability)
        # # Weights are stored in log space too and we only update them when...
        # if prefix in bw:
            # backoff_weight *= (10 ** bw[prefix]) # ...order > 1
        # else:
            # #backoff_weight = 0
            # backoff_weight = backoff_weight

    return 1#[transitionProbability,selfProbability]

def getProbabilities(flavor, historyUnmodified, n, nextTime,selfTransitions):
    global distribution, bucketsTime, bucketsContext, bw,transitionDict,validTargets
    # Init the distribution before each order has a chance to contribute...

    distribution = {}
    # Init the backoff weight to 1.0 for the highest order
    backoff_weight = 1.0
    
    history = []
    selfHistory = []
    for historyIndex, historyPart in enumerate(historyUnmodified):
        history.append('<' + historyPart.split('-')[1])
        selfHistory.append('<' + historyUnmodified[-1].split('-')[1])

    # We already applied the Markov assumption to the history but recall the...
    n = min(len(history) + 1, n) # ...history length can be less than n-1...

    totalProb = 0
    
    
    
    
    currentState = ""
    
    while len(historyUnmodified) > 0 and currentState == "":
        if historyUnmodified[-1].split('-')[-1].replace('>','') in transitionDict:
            currentState = historyUnmodified[-1]
        else:
            del historyUnmodified[-1]
                
        
    cnum = 0
    noncs = 0   
    selfFound = 0
    
    possibleOnes  = []
    

    for checkin in transitionDict[currentState.split('-')[1].replace('>','')]:
        if '-c' not in checkin and not transitionDict[currentState.split('-')[1].replace('>','')][checkin] in possibleOnes:
            possibleOnes.append(transitionDict[currentState.split('-')[1].replace('>','')][checkin])
    # Loop through the orders rather than use recursion
    for order in range(n, 0, -1): # Start at the highest order and walk down
      

      if order == 1:
        # Loop through the unigram distribution
        for token, probability in bucketsContext[0].items():

            if timeData == 1:
                if token != "<s>" and token != "</s>":
                    if version == 0 and currentState != ""  and currentState.split('-')[1].replace('>','') in transitionDict and (token.split('-')[0].replace('>','').replace('<','')+ '-c') in transitionDict[currentState.split('-')[1].replace('>','')] and (transitionDict[currentState.split('-')[1].replace('>','').replace('<','')][token.split('-')[0].replace('>','').replace('<','')+ '-c'] + '-' + nextTime + '>') in bucketsTime[0]:
                        #token = token.split('-')[0].replace('>','') + '-' + transitionDict[currentState.split('-')[1].replace('>','')][token.split('-')[0].replace('<','').replace('>','')] + '>'
                        
                        realToken = "<" + transitionDict[currentState.split('-')[1].replace('>','')][token.split('-')[0].replace('>','').replace('<','')+ '-c'] + '-' + transitionDict[currentState.split('-')[1].replace('>','')][transitionDict[currentState.split('-')[1].replace('>','')][token.split('-')[0].replace('>','').replace('<','')+ '-c']]  +'>'
                        if not realToken in distribution:
                            distribution[realToken] = 0.0
                        distribution[realToken] += backoff_weight * bucketsTime[0][token.split('-')[0].replace('>','') + '-' + nextTime + '>']
                        
                        totalProb += backoff_weight * (bucketsTime[0][token.split('-')[0].replace('>','') + '-' + nextTime + '>'])
                    elif token.split('-')[0].replace('>','').replace('<','') == currentState.split('-')[1].replace('>',''):
                        if not currentState in distribution:
                            distribution[currentState] = 0.0
                        distribution[currentState] += backoff_weight * (10**probability)
                        totalProb += backoff_weight * (10**probability)
                    elif currentState.split('-')[1].replace('>','') in transitionDict and (token.replace('<','').replace('>','')+ '-c') in transitionDict[currentState.split('-')[1].replace('>','')]:    
                        #token = token.replace('>','') + ":" + nextTime + ">"
                        
                        realToken = "<" + transitionDict[currentState.split('-')[1].replace('>','')][token.split('-')[0].replace('>','').replace('<','')+ '-c'] + '-' + transitionDict[currentState.split('-')[1].replace('>','')][transitionDict[currentState.split('-')[1].replace('>','')][token.split('-')[0].replace('>','').replace('<','')+ '-c']]  +'>'
                        #print(validTargets[currentState.split('-')[1].replace('>','')])
                        #print(token)
                        if not realToken in distribution:
                            distribution[realToken] = 0.0
                        distribution[realToken] += backoff_weight * (10**probability)
                        totalProb += backoff_weight * (10**probability)

          # Probabilities are still in log space where we should probably stay
            elif currentState.split('-')[1] in validTargets and token in validTargets[currentState.split('-')[1]]:
                #distribution[token] += backoff_weight * (10 ** probability)
                
                distribution[token] += backoff_weight * (probability)
                totalProb += backoff_weight * (probability)
      else:
         # Update the history by applying the Markov assumption after an...
        history = history[-(order-1):] # ...iteration decrements the order
        selfHistory = selfHistory[-(order-1):] # ...iteration decrements the order
        prefix = ' '.join(history)
        #print(prefix)
        selfPrefix = ' '.join(selfHistory)

        
        
        if prefix not in bucketsContext[order-1] or version == 1:
            
            if (order-1) <= selfTransitions and prefix != selfPrefix:
                if not currentState in distribution:
                    distribution[currentState] = 0.0
                for newToken, newProbability in bucketsContext[order-1][selfPrefix]:
                    if newToken.split('-')[0].replace('>','').replace('<','') == currentState.split('-')[1].replace('>',''):
                        distribution[currentState] += backoff_weight * (10**newProbability)
                        totalProb += backoff_weight * (10**newProbability)
            # ...the orders that don't contain a prefix slice...
            continue # ...will not factor into the interpolation
        for token, probability in bucketsContext[order-1][prefix]:
            
            if timeData == 1:
                if token != "<s>" and token != "</s>":
                    if version == 0 and currentState != ""  and currentState.split('-')[1].replace('>','') in transitionDict and (token.split('-')[0].replace('>','').replace('<','')+ '-c') in transitionDict[currentState.split('-')[1].replace('>','')] and (transitionDict[currentState.split('-')[1].replace('>','').replace('<','')][token.split('-')[0].replace('>','').replace('<','')+ '-c'] + '-' + nextTime + '>') in bucketsTime[0]:
                        #token = token.split('-')[0].replace('>','') + '-' + transitionDict[currentState.split('-')[1].replace('>','')][token.split('-')[0].replace('<','').replace('>','')] + '>'
                        realToken = "<" + transitionDict[currentState.split('-')[1].replace('>','')][token.split('-')[0].replace('>','').replace('<','')+ '-c'] + '-' + transitionDict[currentState.split('-')[1].replace('>','')][transitionDict[currentState.split('-')[1].replace('>','')][token.split('-')[0].replace('>','').replace('<','')+ '-c']]  +'>'

                        if not realToken in distribution:
                            distribution[realToken] = 0.0
                        distribution[realToken] += backoff_weight * bucketsTime[0][token.split('-')[0].replace('>','') + '-' + nextTime + '>']
                        totalProb += backoff_weight * (bucketsTime[0][token.split('-')[0].replace('>','') + '-' + nextTime + '>'])
                    elif token.split('-')[0].replace('>','').replace('<','') == currentState.split('-')[1].replace('>',''):
                        selfFound = 1
                        if not currentState in distribution:
                            distribution[currentState] = 0.0
                        if (order-1) <= selfTransitions and prefix != selfPrefix:
                            for newToken, newProbability in bucketsContext[order-1][selfPrefix]:
                                if newToken.split('-')[0].replace('>','').replace('<','') == currentState.split('-')[1].replace('>',''):
                                    probability = newProbability
                                    
                        distribution[currentState] += backoff_weight * (10**probability)
                        totalProb += backoff_weight * (10**probability)
                    elif currentState.split('-')[1].replace('>','') in transitionDict and (token.replace('<','').replace('>','')+ '-c') in transitionDict[currentState.split('-')[1].replace('>','')]:    
                        #token = token.replace('>','') + ":" + nextTime + ">"
                        realToken = "<" + transitionDict[currentState.split('-')[1].replace('>','')][token.split('-')[0].replace('>','').replace('<','')+ '-c'] + '-' + transitionDict[currentState.split('-')[1].replace('>','')][transitionDict[currentState.split('-')[1].replace('>','')][token.split('-')[0].replace('>','').replace('<','')+ '-c']]  +'>'

                        if not realToken in distribution:
                            distribution[realToken] = 0.0
                        distribution[realToken] += backoff_weight * (10**probability)
                        totalProb += backoff_weight * (10**probability)
                    
          # Probabilities are still in log space where we should probably stay
            else:
                #distribution[token] += backoff_weight * (10 ** probability)
                if not token in distribution:
                            distribution[token] = 0.0
                distribution[token] += backoff_weight * (10 ** probability)
                totalProb += backoff_weight * (10 ** probability)

        #My modification to allow for incomplete data
        if prefix in bw:
            # Weights are stored in log space too and we only update them when...
            backoff_weight *= (10 ** bw[prefix]) # ...order > 1
        else:
            bw_weight = 0
    tokens, probabilities = zip(*[(k, v) for k, v in distribution.items()])
    
    totalProb = 0
    realTokens = []
    realProbabilities = []
    highestStates = {}
    knownTransitions = {}
    transitionContexts = {}



    # else:
    for probIndex, prob in enumerate(probabilities):
        totalProb += prob

    
    tokensRecord, probabilitiesRecord = [list(t) for t in zip(*sorted(zip(tokens, probabilities)))]
    for probIndex, prob in enumerate(probabilitiesRecord):
        probabilitiesRecord[probIndex] = prob/totalProb
    selfProbability = 0
    for token in tokens:
        if token.split('-')[1] == currentState.split('-')[1]:
            selfProbability += probabilitiesRecord[tokens.index(token)]

    del distribution
    return [probabilitiesRecord,tokensRecord,selfProbability,transitionContexts]

def construct_model(flavor,history,length=1):
    conf_json = {}
    conf_json["model"] = MODEL
    conf_json["flavor"] = flavor
    conf_json["history"] = history
    conf_json["length"] =  length
    #conf_json["length"] =  PREDICTION_LENGTH
    with open('request', 'w') as outfile:
        json.dump(conf_json, outfile)

def run_server(t,n,v):
    cmd1 = 'braind ' + t + ' '  + v + ' --order ' + str(n)  
    print("Command: ",cmd1)
    subprocess.check_output(cmd1,  shell = True)

def repeated_tokens(tokens_list):
    prev_pred = ''
    for t in tokens_list:
        if(prev_pred == ''):
            prev_pred = t
        else:
            if(t==prev_pred):
                return True
            else:
                prev_pred = t
    return False
def make_request():
    
    cmd = 'cat request > /tmp/fifo0'
    subprocess.check_output(cmd,  shell = True)
    
    cmd1 = 'cat /tmp/fifo1' 
    binary_object = subprocess.check_output(cmd1,  shell = True)
    output_json = {}
    try:
        output_json = json.loads(binary_object.decode("utf-8"))
    except ValueError:
        print("JSON Decode Error: ", binary_object)
        return -1
    


    return output_json

def kill_server():
    #Get process ID if braind is running
    cmd = 'ps aux | grep -v  grep | grep braind | awk \'{print $2;}\' | cut -d \' \' -f 1'
    cmd_result = subprocess.check_output(cmd,  shell = True)
    pid = cmd_result.decode("utf-8").strip()
    print(pid)
    if len(pid) > 0:
        kill_cmd = 'kill -9 ' + pid  
        subprocess.check_output(kill_cmd,  shell = True)

def create_directory(training_filem,vocab_file,order):
    # Directory where output is saved. 
    final_path= OUTPUT_DIR + os.path.basename(training_file).replace('.txt','') + '-' + os.path.basename(vocab_file).replace('.vocab','')  + '/' + str(order) + 'gram/'

    # REMOVE the folder everytime. The training results will always be saved to the same folder.
    cmd1 = 'rm -rf ' +final_path
    subprocess.check_output(cmd1,  shell = True)

    # Make output directory if it doesn't exist
    if not os.path.exists(final_path):
        os.makedirs(final_path)
        print("Created respective directories.. ")
    
    return final_path


def checkStateViolation(policyElement,fullPolicy,time,useTime,state):
    #global state, unsafeDurationTracker
    unsafeTimeTracker = []
    calculatedTimes = []
    flipTracker = []
    results = []
    causeDescription = []
    for index, part in enumerate(policyElement[0]):
        if type(part) is list:

            if part[0] == "Time":  
                
                if not useTime:
                    continue
                    
                if len(part) == 4:
                    if not '-' in part[1]:
                        initialTime = datetime.time(int(part[1].split(':')[0]),int(part[1].split(':')[1]))
                        results.append(time != initialTime)
                        
                    else:
                        startTime = datetime.time(int(part[1].split('-')[1].split(':')[0]),int(part[1].split('-')[1].split(':')[1])) + datetime.timedelta(minutes=1)
                        endTime = datetime.time(int(part[1].split('-')[0].split(':')[0]),int(part[1].split('-')[0].split(':')[1])) - datetime.timedelta(minutes=1)
                        if startTime < endTime:
                            results.append(time >= startTime and time <= endTime)
                        else:
                            results.append(time <= startTime or time >= endTime)
                    
                else:
                    if not '-' in part[1]:
                        initialTime = datetime.time(int(part[1].split(':')[0]),int(part[1].split(':')[1]))
                        results.append(time == initialTime)
                        
                    else:
                        endTime = datetime.time(int(part[1].split('-')[1].split(':')[0]),int(part[1].split('-')[1].split(':')[1]))
                        startTime = datetime.time(int(part[1].split('-')[0].split(':')[0]),int(part[1].split('-')[0].split(':')[1]))
                        if startTime < endTime:
                            results.append(time >= startTime and time <= endTime)
                        else:
                            results.append(time <= startTime or time >= endTime)
                flipTracker.append(0)
            elif len(part) == 4:
                results.append(not ':'.join([part[0],part[1]]) in state)
                causeDescription.append(part[0] + ":" + part[1] + "NOT")
            else:    
                #results.append(state[part[0]]['state'] == part[1]) 
                results.append(':'.join([part[0],part[1]]) in state)  
                causeDescription.append(part[0] + ":" + part[1] + "WAS")
            flipTracker.append(0)
        else:
            callResult = checkStateViolation(fullPolicy[part],fullPolicy,time,useTime,state)
            results.append(callResult[0])

        if policyElement[-2] == "AND":
            returnCalc = 1
            for resultIndex, resultPart in enumerate(results):
                
                if not resultPart:
                    returnCalc = 0
                    # if flipTracker[resultIndex]:
                        # couldFlip = "AND"
                    # else:
                        # returnCalc = 0
            
        elif policyElement[-2] == "NAND":
            returnCalc = 1
            for resultIndex, resultPart in enumerate(results):
                if not resultPart:
                    # if flipTracker[resultIndex]:
                        # couldFlip = "NAND"
                    returnCalc = 0
            returnCalc = not returnCalc
 
            
        elif policyElement[-2] == "OR":
            returnCalc = 0
            for resultIndex, resultPart in enumerate(results):
                if resultPart:
                    returnCalc = 1
                    # if flipTracker[resultIndex]:
                        # couldFlip = "OR"
                    # else:
                        # returnCalc = 1
            # if returnCalc == 1:
                # couldFlip = "NO"
            # usedInOr = 1
        elif policyElement[-2] == "NOR":
            returnCalc = 0
            for resultIndex, resultPart in enumerate(results):
                if resultPart:
                    # if flipTracker[resultIndex]:
                        # couldFlip = "NOR"
                    returnCalc = 1
            # if returnCalc == 1:
                # couldFlip = "NO"
            returnCalc = not returnCalc
            usedInNor = 1
        elif policyElement[-2] == "XOR":
            returnCalc = results[0]
            for resultIndex, resultPart in enumerate(results):
                # if flipTracker[resultIndex] == 1:
                    # couldFlip = "XOR"
                if resultIndex != 0:
                    returnCalc = returnCalc != resultPart
            #usedInXor = 1 
        else:
            # positives = 0
            # flippables = 0
            returnCalc = results[0]
            for resultIndex, resultPart in enumerate(results):
                # if flipTracker[resultIndex]:
                    # couldFlip = "XNOR"
                    # flippables += 1
                # if resultPart and not flipTracker[resultIndex]:
                    # positives += 1
                if resultIndex != 0:
                    returnCalc = returnCalc == resultPart
            # if not returnCalc and positives > 0 and len(results) - positives > flippables:
                # couldFlip = "NO"

        # if couldFlip == "NO":
            # return [returnCalc,[]]
        # else:
            # unsafeTimeTracker.append(couldFlip)
            # if len(unsafeTimeTracker) > 0 and starting == 1 and returnCalc == 1:
                # target = 1
        return [returnCalc,causeDescription]
    
pathnum = 0   
testTotal = 0 
historyDiffLimit = 0
rememberedPaths = 0
pathTracker = {}


addedIn1 = 0
addedIn2 = 0
addedIn3 = 0
addedIn4 = 0
addedIn4Num = 0
averageSelfTransitions = 0
averageNewStates = 0
whentotrack = 0
def explore_path(state,historiesList, currentWait, currentProb, coreWaitTime, paths, selfTransitions,lineIndex,durationTrackerTemp,limitedTrackerTemp,newEventsTemp,currentRecordHistoryTemp):
    global visitedStates, unsafeStateThreshold, timeSteps, unsafeStates, modWait, mod, pathnum, validPathsForHistory,testTotal, pathTracker, rememberedPaths, validPathsForHistoryTest, historyGroupSize, minimumProabilityFactor, historyDiffLimit, timeData,max_dict_size
    global addedIn1,addedIn2,addedIn3,addedIn4,addedIn4Num,eventTranslations,limitedActionsTracker,relevantActionsTracker
    global numberExplored, averageSelfTransitions, averageNewStates, runtimeStart, contextTranslations, eventPredictionDict, eventPartTracker,whentotrack, overallPredicates
    stateSplit = state.replace('<','').replace('>','').split('-')
    stateTimeless = "<" + stateSplit[0] + '-' + stateSplit[1] +">"

    if selfTransitions == 0 and stateTimeless in relevantActionsTracker:
        for combo in relevantActionsTracker[stateTimeless]:
            deleted = 0
            if len(limitedTrackerTemp[combo][2]) >= limitedTrackerTemp[combo][0]:
                for arrayIndex in range(len(limitedTrackerTemp[combo][2])):
                    if lineIndex - limitedTrackerTemp[combo][2][arrayIndex-deleted] > limitedTrackerTemp[combo][1]:
                        del limitedTrackerTemp[combo][2][arrayIndex-deleted]
                        deleted += 1
            limitedTrackerTemp[combo][2].append(lineIndex)
            if len(limitedTrackerTemp[combo][2]) > limitedTrackerTemp[combo][0]:
                limitedActionsTracker[combo][4] += currentProb

    for eventPart in newEventsTemp:
        #eventPartSplit = eventPart.split(':')
        if eventPart == "NONE":
            continue
        eventPartSplit = eventPart.split('-')[1].split(':')
        if eventPartSplit[0] in durationTrackerTemp and eventPartSplit[1] in durationTrackerTemp[eventPartSplit[0]]:
            durationTrackerTemp[eventPartSplit[0]][eventPartSplit[1]] = lineIndex + currentWait
 
    stateTimeSplit = stateSplit[2].split(':')
    if stateTimeSplit[1] != '59':
        stateTimeNext = stateTimeSplit[0] + ':' + str(int(stateTimeSplit[1])+1)
    else:
        stateTimeNext = str((int(stateTimeSplit[0])+1)%24) + ':00'
    stateContextHour= "<" + stateSplit[1] + '-' + stateTimeSplit[0] + ">"
    
    if currentWait == timeSteps:
       del durationTrackerTemp
       return []
    waitTimePredicted = currentWait + 1
    pathnum += 1

    unsafeStateProbAddition = {}
    #Code for rounding wait time to 10
    
    
    identity = (state + str(int(math.ceil(waitTimePredicted / historyGroupSize)) * historyGroupSize))
    skip = 0
    relevantHistoryRecord = 1
   
        
    #if 1== 1 or skip == 0:
    if skip == 0:
      pathList = []
      numberExplored += 1
      #records = mod["interpolate"]("up", thisHistory, 1)
      totalProbability = 0
      
      partIndex = []
      averageNoTransition = []
      

      newHistoriesList = {}
      newHistoriesListReal = {}
      timeIn1 = 0
      timeIn2 = 0
      timeIn3 = 0
      timeTotal = 0
      lowestNumberHere = 1
      totalHistory = 0
      timeSplit1 = 0
      timeSplit2 = 0
      timeSplit3 = 0
      bigTime1 = 0
      bigTime2 = 0
      bigTime3 = 0
      minProb = 1
      
      # if len(historiesList) > 1000:
        # minProb = 1/historiesList
      # for historyToTestIndex, historyToTestArray in enumerate(historiesList): 
          # if historiesList[historyToTestArray] < minProb:
            # continue
          # #print(historyToTestIndex)
          # probDict = []
          # time1 = time.time()
          # historyToTest = historyToTestArray.split(',')
          # smallerHistoryTemp = historyToTest
          # if len(smallerHistoryTemp) >= order:
                # del smallerHistoryTemp[0]
          # smallerHistory = ','.join(smallerHistoryTemp)
          # if not smallerHistory in newHistoriesList:
            # newHistoriesList[smallerHistory] = [[],0,{},0]
          # newHistoriesList[smallerHistory][3] += historiesList[historyToTestArray]
          # currentStateRecordCheck = contextTranslations[int(historyToTest[-1].replace('<','').replace('>',''))].split(',')
          # time2 = time.time()
          # bigTime1 += time2 - time1
      #currentStateRecordTemp = currentRecordHistoryTemp[-1].copy()
      currentStateRecordTemp = overallPredicates.copy()
      eventProbabillities = {}
      totalProbabilitiyHere = 0
      for modelPart in eventPredictionDict:
        modelPartSplit = modelPart.split(':')
        if eventPredictionDict[modelPart][0] == []:
            if currentRecordHistoryTemp[-1]["total"] == -1:
                currentStateRecordTemp[modelPart.split('-')[1]] = 100
            else:
                currentStateRecordTemp[modelPart.split('-')[1]] = currentRecordHistoryTemp[-1][modelPart.split('-')[1]]
            continue
        resultsHere = getProbabilitiesFromDict(modelPart,currentRecordHistoryTemp[-1],len(currentRecordHistoryTemp),stateTimeSplit,currentStateRecordTemp,lineIndex)
        # for resultsAdding in resultsHere[0]:
            # currentStateRecordTemp[resultsAdding] += resultsHere[0][resultsAdding]
        # currentStateRecordTemp["total"] += resultsHere[1]
        # eventProbabillities[modelPartSplit[0].split("-")[1] + ',' + modelPartSplit[1]] = resultsHere[0]
        # totalProbabilitiyHere += resultsHere[0] + resultsHere[1]
      # for modelPart in eventPredictionDict:   
        # modelPartSplit = modelPart.split(':')
        # currentStateRecordTemp[modelPartSplit[0].split("-")[1]][modelPartSplit[1]] =  eventProbabillities[modelPartSplit[0].split("-")[1] + ',' + modelPartSplit[1]]/totalProbabilitiyHere
      for overallElem in currentStateRecordTemp:
        if overallElem ==  'total' or overallElem == "otherTotals":
            continue
        if not ',' in overallElem:
            currentStateRecordTemp[overallElem] = currentStateRecordTemp[overallElem]/currentStateRecordTemp["total"]
        else:
            currentStateRecordTemp[overallElem] = currentStateRecordTemp[overallElem]/currentStateRecordTemp["otherTotals"][overallElem.split(',')[0].split(':')[0] + ',' +overallElem.split(',')[1].split(':')[0]]
      
      if len(currentRecordHistoryTemp) == 0:
            currentRecordHistoryTemp.append(currentStateRecordTemp.copy())
      elif len(currentRecordHistoryTemp) < order:
            currentRecordHistoryTemp.append(currentStateRecordTemp.copy())
      else:
            del currentRecordHistoryTemp[0]
            currentRecordHistoryTemp.append(currentStateRecordTemp.copy())
            
            
            # if not modelPart in newHistoriesList[smallerHistory][2]:
            # newHistoriesList[smallerHistory][2][modelPart] = 0
        # newHistoriesList[smallerHistory][2][modelPart] += tempProb
        # probDict.append([[modelPart],tempProb])
        # partIndex.append(modelPart.split('-')[1])
        # totalProbability += tempProb
        # newHistoriesList[smallerHistory][1] += tempProb
      # selfProbabilityHere = statistics.mean(averageNoTransition)
      # newHistoriesList[smallerHistory][0] .append(selfProbabilityHere)
      # time3 = time.time()
      # bigTime2 += time3 - time2
      # for historyToTestIndexSmall, smallHist in enumerate(newHistoriesList):
          # selfProbabilityHere = statistics.mean(newHistoriesList[smallHist][0])
          
          # probOfTransition = 1 - selfProbabilityHere
          # time2 = time.time()
          # probDict = []
          # #for probIndex, prob in enumerate(probDict):
            # #probDict[probIndex][1] = (probDict[probIndex][1]/totalProbability) * probOfTransition
          # for histPart in newHistoriesList[smallHist][2]:
            # #newHistoriesList[smallHist][2][histPart] = (newHistoriesList[smallHist][2][histPart]/newHistoriesList[smallHist][1] ) * probOfTransition
            # probDict.append([[histPart],(newHistoriesList[smallHist][2][histPart]/newHistoriesList[smallHist][1] ) * probOfTransition])
            
                
          # probDict.insert(0,[[],selfProbabilityHere])
          # selfTransitionModificationAmount = 0
          # statesToExplore = []
          # newUnsafe = 0
          # saveable = 1
          # tempHistoryTracker = {}
          # time3 = time.time()
          # # if (currentWait + 1) == timeSteps:
            # # totalHistory += newHistoriesList[smallHist][3]
            # # print(smallHist)
            # # print(newHistoriesList[smallHist][3])
            # # print()
          
          
      # for unsafeActionIndex, unsafeAction in enumerate(probDict):
          # timeSplitStart = time.time()
          # if unsafeActionIndex == 0:
            # unsafeRecord = smallHist.split(',')[-1]

          # else:
            # currentStateRecordCalc = contextTranslations[int(historyToTest[-1].replace('<','').replace('>',''))].split(',').copy()
            # for actionToTake in unsafeAction[0]:

                # currentStateRecordCalc[int(actionToTake.split('-')[0])] = actionToTake.split('-')[1]
            # timeSplitPart1 = time.time()
            # if not ','.join(currentStateRecordCalc) in contextTranslations:
              # contextTranslations.append(','.join(currentStateRecordCalc))
              # unsafeRecord = '<' + str(contextTranslations.index(','.join(currentStateRecordCalc))) + '>'
      for unsafeIndex, unsafeState in enumerate(unsafeTranslations):
        unsafeStateProbAddition["<" + str(unsafeIndex) + ">"] = checkStateViolationFromProbabilities(unsafeTranslations[unsafeState]['0'],unsafeTranslations[unsafeState],currentRecordHistoryTemp[-1])
        #unsafeRecord = '<' + str(contextTranslations.index(','.join(currentStateRecordCalc))) + '>'
        
        # if checkViolationsResult[0]:
            # violatingTimes = []
            # if len(unsafeTranslations[unsafeState]['0'][1]) > 0:
                # for timeCheckIndex, timeCheck in enumerate(unsafeTranslations[unsafeState]['0'][1]):
                    # if (timeCheck[1] == 0 or timeCheck[1] == 2) and checkStateViolation(unsafeTranslations[unsafeState]['0'],unsafeTranslations[unsafeState],(timeCheck[0]-datetime.timedelta(minutes=1)).time(),1,currentStateRecordCalc)[0]:
                        # if timeCheckIndex == 0:
                            # startMod = unsafeTranslations[unsafeState]['0'][1][-1][0] + datetime.timedelta(minutes=1)
                            # startBound = str(startMod.hour) + ':' + str(startMod.minute)
                        # else:
                            # startMod = unsafeTranslations[unsafeState]['0'][1][timeCheckIndex-1][0] + datetime.timedelta(minutes=1)
                            # startBound = str(startMod.hour) + ':' + str(startMod.minute)
                        # endBound = str((timeCheck[0]-datetime.timedelta(minutes=1)).hour) + ':' + str((timeCheck[0]-datetime.timedelta(minutes=1)).minute)
                        # violatingTimes.append(startBound + '/' + endBound)
                    # if (timeCheck[1] == 0 or timeCheck[1] == 2) and checkStateViolation(unsafeTranslations[unsafeState]['0'],unsafeTranslations[unsafeState],(timeCheck[0]).time(),1,currentStateRecordCalc)[0]:
                        # if timeCheck[1] == 2:
                            # startBound = str(timeCheck[0].hour) + ':' + str(timeCheck[0].minute)
                            # endBound = str(timeCheck[0].hour) + ':' + str(timeCheck[0].minute)
                        # else:
                            # startBound = str(timeCheck[0].hour) + ':' + str(timeCheck[0].minute)
                            # endMod = unsafeTranslations[unsafeState]['0'][1][timeCheckIndex + 1][0]
                            # endBound = str(startMod.hour) + ':' + str(startMod.minute)
                        # violatingTimes.append(startBound + '/' + endBound)
                    # if (timeCheck[1] == 1 or timeCheck[1] == 2) and checkStateViolation(unsafeTranslations[unsafeState]['0'],unsafeTranslations[unsafeState],(timeCheck[0]-datetime.timedelta(minutes=1)).time(),1,currentStateRecordCalc)[0]:
                        # if timeCheckIndex == len(unsafeTranslations[unsafeState]['0'][1]) - 1:
                            # endMod = unsafeTranslations[unsafeState]['0'][1][0][0] - datetime.timedelta(minutes=1)
                            # endBound = str(startMod.hour) + ':' + str(startMod.minute)
                        # else:
                            # endMod = unsafeTranslations[unsafeState]['0'][1][timeCheckIndex+1][0] - datetime.timedelta(minutes=1)
                            # endBound = str(startMod.hour) + ':' + str(startMod.minute)
                        # startBound = str((timeCheck[0]+datetime.timedelta(minutes=1)).hour) + ':' + str((timeCheck[0]+datetime.timedelta(minutes=1)).minute)
                        # violatingTimes.append(startBound + '/' + endBound)
                # if len(violatingTimes) == 0:
                    # continue
            # unsafeStateProbAddition[unsafeRecord.replace('>','').replace('<','')] = transitionProb
                    # unsafeStates[unsafeRecord.replace('<','').replace('>','')] = [-1,violatingTimes]
                    # unsafeStateReasons[unsafeRecord.replace('<','').replace('>','')] = [checkViolationsResult[1]]
                    # if not unsafeRecord.replace('<','').replace('>','') in unsafeStateTypeTracker:
                        # unsafeStateTypeTracker[unsafeRecord.replace('<','').replace('>','')] = []
                    # unsafeStateTypeTracker[unsafeRecord.replace('<','').replace('>','')].append(str(unsafeIndex))
                    # newUnsafe = 1
            #unsafeRecord = str(contextTranslations.index(','.join(currentStateRecordCalc)))
            
              # timeSplitPart2 = time.time()
              # #transitionProb = ((unsafeAction[1] + selfTransitionModificationAmount)) * historiesList[historyToTestArray]
              # transitionProb = ((unsafeAction[1] + selfTransitionModificationAmount)) * newHistoriesList[smallHist][3]
              # if (unsafeRecord.replace('<','').replace('>','')) in unsafeStates and checkIfUnsafeTime(unsafeRecord.replace('<','').replace('>','') + "-" + stateTimeNext,durationTrackerTemp,lineIndex + waitTimePredicted):
                # if (currentWait + 1) == timeSteps:
               

                  # testTotal += transitionProb
                  # unsafeStateProbAddition[unsafeRecord.replace('>','').replace('<','')] = transitionProb
                # else:
                    # historyToTest = smallHist.split(',').copy()
                    # historyToTest.append('<' + unsafeRecord + '>')
                    # if not ','.join(historyToTest) in newHistoriesListReal:
                        # newHistoriesListReal[','.join(historyToTest)] = 0
                    # newHistoriesListReal[','.join(historyToTest)] += transitionProb
                 
              # else:
                
                # historyToTest = smallHist.split(',').copy()
                # historyToTest.append('<' + unsafeRecord.replace('<','').replace('>','') + '>')
                # if not ','.join(historyToTest) in newHistoriesListReal:
                        # newHistoriesListReal[','.join(historyToTest)] = 0
                # newHistoriesListReal[','.join(historyToTest)] += transitionProb
              # timeSplitPartFinal = time.time()
              # # timeSplit1 += timeSplitPart2 - timeSplitStart
              # # timeSplit2 += timeSplitPart2 - timeSplitPart1
              # # timeSplit3 += timeSplitPartFinal - timeSplitPart2
      
          #addedIn4 += transitionProb
      # if (currentWait + 1) == timeSteps:
        # print(totalHistory)
      # timeFinal = time.time()
      # bigTime3 += timeFinal - time3
      # print(time2 -  time1)
      # print(time3 -  time2)
      # print(timeFinal -  time3)
      # print(bigTime1)
      # print(bigTime2)
      # print(bigTime3)
      # print()
      tempUnsafeStateThreshold = explore_path('<0-0' + '-' + stateTimeNext + '>',newHistoriesListReal,waitTimePredicted,0,coreWaitTime,pathList,selfTransitions,lineIndex,durationTrackerTemp.copy(),limitedTrackerTemp.copy(), [],currentRecordHistoryTemp.copy())
      
      

      for thresh in tempUnsafeStateThreshold:
         if thresh in  unsafeStateProbAddition:
            unsafeStateProbAddition[thresh] += tempUnsafeStateThreshold[thresh]
         else:
            unsafeStateProbAddition[thresh] = tempUnsafeStateThreshold[thresh]
      recordedProbs = unsafeStateProbAddition.copy()

    
    if currentWait == 0:
        probTotal = 0
        highestProb = 0
        highestProbState = ""
        for prob in unsafeStateProbAddition:
            probTotal += unsafeStateProbAddition[prob]
            if unsafeStateProbAddition[prob] > highestProb:
                highestProb = unsafeStateProbAddition[prob]
                highestProbState = prob

        del durationTrackerTemp
        return [unsafeStateProbAddition,highestProbState]

    else:
        del durationTrackerTemp
        return unsafeStateProbAddition
            
    

    
    


unsafeStateThreshold = -1
timeSteps = -1
unseenTransitionsNotUnsafe = {}
if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Provide the directory from which sequence of tokens need to be generated.')
    parser.add_argument('training_file_wait', type=argparse.FileType('r'))
    parser.add_argument('training_file', type=argparse.FileType('r'))
    parser.add_argument('-o', '--order', type=int, default=3)
    parser.add_argument('-v', '--vocab', type=argparse.FileType('r'))
    parser.add_argument('-n', '--timeStepLength', type=int, default=1)
    #parser.add_argument('-t', '--trainLength', type=int, default=100)
    parser.add_argument('-t', '--trainLength', type=float, default=0.30)
    parser.add_argument('-r', '--traceLength', type=int, default=2)
    #parser.add_argument('-e', '--evalLength', type=int, default=100)
    parser.add_argument('-u', '--unsafeStates', type=int, default=10)
    parser.add_argument('-s', '--timeSteps', type=int, default=3)
    parser.add_argument('-p', '--unsafeStateThreshold', type=float, default=0.1)
    parser.add_argument('-m', '--minimumProabilityFactor', type=float, default=0.001)
    parser.add_argument('-l', '--historyDiffLimit', type=float, default=0.001)
    parser.add_argument('-e', '--evalFile', type=argparse.FileType('r'))
    parser.add_argument('-g', '--historyGroupSize', type=int, default=10)
    parser.add_argument('-i', '--timeData', type=int, default=0)
    parser.add_argument('-pn', '--policyNum', type=int, default=0)
    parser.add_argument('-sn', '--stateNum', type=int, default=0)
    parser.add_argument('-ds', '--depthSize', type=int, default=0)
    parser.add_argument('-dr', '--durations', type=int, default=0)
    parser.add_argument('-vr', '--version', type=int, default=0)
    parser.add_argument('-un', '--unseenStates', type=int, default=-1)
    args = parser.parse_args()
    unsafeStates = {}
    limitedActionsTracker = {}
    relevantActionsTracker = {}
    unsafeStateAccuracy = {}
    unsafeStateAccuracyChecker = {}
    unsafeStateAccuracyChecker2 = {}
    unsafeStateTypeTracker = {}
    unsafeStateReasons = {}
    probabilityAccuracy = {}
    predictionOfUnseenAccuracy = {}
    numberExplored = 0
    lowestThreshold = {}
    predictionRecord = []
    unsafeDoneTracker = {}
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/unsafeStateTranslations.txt", "rb") as myFile:
        unsafeTranslations = pickle.load(myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/largestTransitions.txt", "rb") as myFile:
        largestTransitions = pickle.load(myFile)
    for checkedUnsafeState in unsafeTranslations:
        if unsafeTranslations[checkedUnsafeState]["Duration"] == 1:
            for level in unsafeTranslations[checkedUnsafeState]:
                if level == "Duration":
                    continue
                
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/allowedTransitions.txt", "rb") as myFile:
        allowedTransitions = pickle.load(myFile)           
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/eventTranslations.txt", "rb") as myFile:
        eventTranslations = pickle.load(myFile)
    for eventID in eventTranslations:
        eventPartTracker.append(eventID.split(','))
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/contextTranslations.txt", "rb") as myFile:
        contextTranslations = pickle.load(myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/durationRecords.txt", "rb") as myFile:
        unsafeDurationTracker = pickle.load(myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/transitionsInTraining2.txt", "rb") as myFile:
        transitionsInTraining = pickle.load(myFile)

    for durationPart in unsafeDurationTracker:
        for arrayPart in unsafeDurationTracker[durationPart][0]:
            if not arrayPart[0] in durationTracker:
               durationTracker[arrayPart[0]] = {}
            if not arrayPart[1] in durationTracker[arrayPart[0]]:
               durationTracker[arrayPart[0]][arrayPart[1]] = None
    
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/predictionDict2.txt", "rb") as myFile:
        eventPredictionDict = pickle.load(myFile)    
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/overallPredicates.txt", "rb") as myFile:
        overallPredicates = pickle.load(myFile)    
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/predicateList.txt", "rb") as myFile:
        predicateList = pickle.load(myFile)    
    limitedActionsTracker = {}
    unseenStatesMain = str(args.unseenStates)
    unsafeDoneTrackerHere = {}
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/unsafeStateFile.csv", "r") as unsafe_file:
        for lineIndex, line in enumerate(list(unsafe_file)):
            if lineIndex == 0:
                unsafeList = line.split(',')
                for unsafeState in unsafeList:
                    unsafeStateSplit = unsafeState.split('-')
                    if unsafeStateSplit[0] == '\n':
                        continue
                    
                    unsafeStates[unsafeStateSplit[1]] = [-1, []]
                    probabilityAccuracy[unsafeStateSplit[1]] = {"AverageProbability": [], "Positive": 0, "Predictions": 0, "PredictionDone": 0}
                    for unsafeStateElementIndex, unsafeStateElement in enumerate(unsafeStateSplit):
                        if unsafeStateElementIndex == 3:
                            timeSplit = unsafeStateElement.split('/')
                            firstTime = datetime.time(hour=int(timeSplit[0].split(':')[0]),minute=int(timeSplit[0].split(':')[1]))
                            secondTime = datetime.time(hour=int(timeSplit[1].split(':')[0]),minute=int(timeSplit[1].split(':')[1]))
                            unsafeStates[unsafeStateSplit[1]][1].append([firstTime,secondTime])
                            

                    if not unsafeStateSplit[1] in unsafeStateTypeTracker:
                        unsafeStateTypeTracker[unsafeStateSplit[1]] = []
                        
                        unsafeStateReasons[unsafeStateSplit[1]] = unsafeStateSplit[4:]
                    if not unsafeStateSplit[2].replace('\n','') in unsafeStateTypeTracker[unsafeStateSplit[1]]:
                        unsafeStateTypeTracker[unsafeStateSplit[1]].append(unsafeStateSplit[2].replace('\n',''))
                        unsafeDoneTracker[unsafeStateSplit[2].replace('\n','')] = 0

                    unsafeStateAccuracyChecker[str(unsafeStateSplit[0]).replace('\n','') ]  = 0
                    unsafeStateAccuracyChecker2[str(unsafeStateSplit[0]).replace('\n','')]  = 0
                unsafeStateAccuracy = {"Occurances": 0,  "False Positives": 0, "False Negatives": 0, "True Positives": 0, "True Negatives": 0,"Predictions": 0}
            elif ',' in line:
                continue
                lineSplit = line.split(",")
                comboPortion = lineSplit[0].split(":")
                actionCombo = comboPortion[0]# + comboPortion[1]
                if  ':' in lineSplit[1]:
                    relevantStates = lineSplit[1].split(':')
                else:
                    relevantStates = [lineSplit[1]]
                assembledStates = []
                for state in relevantStates:
                    
                    adjustedState = "<" + str(state).replace('\n','') + ">"
                    if not adjustedState in relevantActionsTracker:
                        relevantActionsTracker[adjustedState] = []
                    if not actionCombo in relevantActionsTracker[adjustedState]:
                        relevantActionsTracker[adjustedState].append(actionCombo)
                limitedActionsTracker[actionCombo] = [int(comboPortion[2]),int(comboPortion[3]),[],0]
                
    individualAccuracyTracker = {}
    
    order = args.order

    #input_file = args.scenarios_file.name
    training_file_wait = args.training_file_wait.name
    training_file = args.training_file.name
    vocab_file = args.vocab.name
    #numStates = args.numStates
    timeStepLength = args.timeStepLength
    trainingSize = args.trainLength
    traceLength = args.traceLength
    #evalSize = args.evalLength
    evalFile = args.evalFile.name
    unsafeStateNum = args.unsafeStates
    timeSteps =  args.timeSteps
    unsafeStateThreshold = args.unsafeStateThreshold
    historyGroupSize = args.historyGroupSize
    minimumProabilityFactor = args.minimumProabilityFactor
    historyDiffLimit = args.historyDiffLimit
    timeData = args.timeData
    policyNum = args.policyNum
    stateNum = args.stateNum
    depthSize = args.depthSize
    durations= args.durations
    version = args.version
    if unsafeStateThreshold == -1 or timeSteps == -1:
        print("Error Inputs")
        exit()

    print("Start.......")
    trainingSplit = training_file.split("/")
    if "random" in trainingSplit[-1]:
        highestState = 0
        with open(vocab_file,'r',encoding="utf-8-sig") as fromFile:
            for line in fromFile:
                line = line.replace('<','').replace('>','').replace('\n','')
                if int(line) > highestState:
                    highestState = int(line)
                         

    output_path = create_directory(training_file,vocab_file,order)
    op = ['-v', vocab_file, '-o', str(order), '-s', "ModKN"]


    mitlmi = ['estimate-ngram', '-t', training_file, '-wl', 'ilmTime']
        
           
    ilmTime  = model.Ngram('ilmTime', 'interpolate')
    
    modTime  = {"interpolate" : ilmTime.stream }
    
    ilmTime2  = model.Ngram('ilmTime', 'backoff')
    
    modTime2  = {"backoff" : ilmTime2.stream }
    
    ilmTime3  = model.Ngram('ilmTime', 'fake')
    
    modTime3  = {"fake" : ilmTime3.stream }
    
    bucketsTime = modTime2["backoff"]("up", [], 1)[0]

        
           
    
    
    ilmContext  = model.Ngram('/home/man5336/Documents/ProvPredictor/EvalFolder/ilmContext', 'interpolate')
    
    modContext  = {"interpolate" : ilmContext.stream }
    
    ilmContext2  = model.Ngram('/home/man5336/Documents/ProvPredictor/EvalFolder/ilmContext', 'backoff')
    
    modContext2  = {"backoff" : ilmContext2.stream }
    
    ilmContext3  = model.Ngram('/home/man5336/Documents/ProvPredictor/EvalFolder/ilmContext', 'fake')
    
    modContext3  = {"fake" : ilmContext3.stream }
    
    distribution = modContext["interpolate"]("up", [], 1)[0]
    bucketsContext = modContext2["backoff"]("up", [], 1)[0]

    bw = modContext3["fake"]("up", [], 1)[0]
    getTransitionDict()
    cleanDistribution()
    
    groundString = ""
    unseenProbabilityGround = 0
    stateRecords = []
    transitionRecords = []
    transitionStates = []
    transitionStatesProbabilities = []
    transitionAvg = 0
    transitionDiffAvg = 0
    transitionDiffAvg = 0
    unseenDiffAvg = 0
    unseenPredictedAvg = 0
    overallTransitionDifAvg = 0
    overallUnseenDifAvg = 0
    overallTransitionAvg = 0
    tranAverageList = []
    unseenAverageList = []
    tranTotalAverageList = []
    selfTransitionProbRemovedSpace = 0
    selfTransitionState = ""

    transitionProbabilityListBuilder = {}



        
             

currentPassed = 0
unsafeOccured = 0
unsafeOccured2 = 0
evalList = []

predictedCount = 0
notPredictedCount = 0


with open(evalFile, "r") as eval_file:
        evalList = list(eval_file)
currentState = -1
lastState = None
historySize = 0
waitTimePredicted = 0
runtimeStart = time.time()
predictionTime = -1
selfTransitionTracker = 1


thereIsPositive = 0
modHistory = []
startingContext = evalList[0].replace('\n','').split(',')
for durationPart in durationTracker:
    for stateName in durationTracker[durationPart]:
        if startingContext[durationPart] == stateName:
            durationTracker[durationPart][stateName] = 0
stateOccuranceTracker = {}

positives = 0
negatives = 0
predictionsTracker = -1

#currentStateRecord = overallPredicates.copy()
currentStateRecord = {"total": -1}
currentRecordTracker = {}
recordHistory = []
# for modelPart in eventPredictionDict:
    # modelPartSplit = modelPart.split('-')[1].split(':')
    # if not modelPartSplit[0] in currentStateRecord:
        # currentStateRecord[modelPartSplit[0]] = {}
    # currentStateRecord[modelPartSplit[0]][modelPartSplit[1]] = 0
for lineIndex, line in enumerate(evalList):
    if lineIndex + timeSteps >= len(evalList) -1:
        break
    if lineIndex == 0:
        # currentStateRecord = line.replace('\n','').split('~')[1].split(',')
        for part in line.replace('\n','').split('~')[1].split(','):
            currentStateRecord[part.split(':')[0]] = part.split(':')[1]
            #currentStateRecord[part] = 1
            #currentRecordTracker[part.split(':')[0]] = part.split(':')[1]
        currentStateRecord["total"] = -1
        continue
    if lineIndex > 2000:
       break
    line = line.replace('\n','')
    lineSplit = line.split('~')
    currentState = lineSplit[1]
    currentRecordUpdate = lineSplit[0].split(',')


    currentStateSplit = currentState.split('-')
    
    
        
    for partHere in lineSplit[0].split(','):
        partHereSplit = partHere.split('-')[1]
        
        #currentStateRecord[partHereSplit.split(":")[0] + ':' + currentRecordTracker[partHereSplit.split(":")[0]]] = 0
        currentStateRecord[partHereSplit.split(":")[0]] =  partHereSplit.split(":")[1]
        #currentRecordTracker[partHereSplit.split(":")[0]] = partHereSplit.split(":")[1]
        #currentStateRecord[partHereSplit] = 1

    # for deviceState in contextTranslations[int(currentStateSplit[1])].split(','):
        # deviceStateSplit = deviceState.split(':')
        # for recordHere in currentStateRecord[deviceStateSplit[0]]:
            # currentStateRecord[deviceStateSplit[0]][recordHere] = 0
        # currentStateRecord[deviceStateSplit[0]][deviceStateSplit[1]] = 1
    nextTime = ""
    for eventPart in currentStateSplit:
        eventPartSplit = eventPart.split(':')
        if eventPartSplit[0] in durationTracker and eventPartSplit[1] in durationTracker[eventPartSplit[0]]:
            durationTracker[eventPartSplit[0]][eventPartSplit[1]] = lineIndex
    if currentStateSplit[-1].split(':')[1] == "59":
        nextTime = str((int(currentStateSplit[-1].split(':')[0])+1)%24) + ':' + currentStateSplit[-1].split(':')[1]
    else:
        nextTime = currentStateSplit[-1].split(':')[0] + ':' + str(int(currentStateSplit[-1].split(':')[1])+1)
    currentStateMod = "<" + currentState + ">"
    currentStateTimeless = currentStateSplit[0] + '-' + currentStateSplit[1]
    currentStateTimelessMod = "<" + currentStateTimeless + ">"
    if currentStateTimelessMod in relevantActionsTracker:
       
        for combo in relevantActionsTracker[currentStateTimelessMod]:
            if len(limitedTrackerTemp[combo][2]) > limitedTrackerTemp[combo][0]:
                deleted = 0
                for arrayIndex in range(len(limitedActionsTracker[combo][2])):
                    if lineIndex - limitedActionsTracker[combo][2][arrayIndex-deleted] > limitedActionsTracker[combo][1]:
                        del limitedActionsTracker[combo][2][arrayIndex-deleted]
                        deleted += 1
            limitedActionsTracker[combo][2].append(lineIndex)
    for combo in limitedActionsTracker:
        limitedActionsTracker[combo][3] = 0
    currentPassed += 1
    
    wannaPrint = 0
    # if len(recordHistory) >= 1:
        # for recordElem in currentStateRecord:
            # #print(currentStateRecord)
            # #print(recordHistory[-1])
            # if currentStateRecord[recordElem] != recordHistory[-1][recordElem]:
                # wannaPrint = 1
                # print(recordElem)
                # print(lineIndex)
                # print()
    
    if lastState == currentStateTimeless:
       # selfTransitionTracker += 1
        selfTransitionTracker += 0
    else:
        selfTransitionTracker = 1
        if historySize == 0:
            modHistory = ["<" + currentStateTimeless.split('-')[1] + ">"]
            history = ["<" + currentStateTimeless + ">"]
            historySize += 1
            recordHistory.append(currentStateRecord.copy())
        elif historySize < order:
            modHistory.append("<" + currentStateTimeless.split('-')[1] + ">")
            history.append("<" + currentStateTimeless + ">")
            recordHistory.append(currentStateRecord.copy())
            historySize += 1
        else:
            del history[0]
            del modHistory[0]
            del recordHistory[0]
            modHistory.append("<" + currentStateTimeless.split('-')[1] + ">")
            history.append("<" + currentStateTimeless + ">")
            recordHistory.append(currentStateRecord.copy())
        if currentStateTimeless.split('-')[1] in unsafeStates and checkIfUnsafeTime(currentState.split('-')[1] + '-' + currentState.split('-')[2],durationTracker,lineIndex + waitTimePredicted):
            unsafeStateAccuracy["Occurances"] += 1
    historyString = ','.join(modHistory)
    historyString = modHistory[-1]
    if lastState != None and (not currentStateTimeless.split('-')[1] in unsafeStates or not checkIfUnsafeTime(evalList[lineIndex].replace('\n','').split('~')[1].split('-')[1] + '-' + evalList[lineIndex].replace('\n','').split('~')[1].split('-')[2] ,durationTracker,lineIndex + waitTimePredicted)):
        for unsafeState in unsafeStates:
            unsafeStates[unsafeState][0] = 0
        visitedStates = {}
        if not historyString in individualAccuracyTracker:
            individualAccuracyTracker[historyString] = {"AverageProbability": {}, "Positive": {}, "Predictions": 0, "AccuracyTracker": {}}
        individualAccuracyTracker[historyString]["Predictions"] += 1

        startTime = time.time()
        waitTimePredicted = 0
        

      
        # timeCheckHour = int(currentStateSplit[2].split(':')[0])
        # timeCheckMinute = int(currentStateSplit[2].split(':')[1]) + timeSteps
        # timeCheckFinal = 0
        # while timeCheckMinute > 59:
            # timeCheckMinute = timeCheckMinute % 60
            # timeCheckHour += 1
        # if timeCheckHour > 23:
            # timeCheckHour = timeCheckHour % 24
        # if timeCheckHour >= 22 or timeCheckHour < 6 or (timeCheckHour == 6 and timeCheckMinute == 0):
            # timeCheckFinal = 1
        # if timeCheckFinal == 1:

        
        
        returnArray = explore_path(currentStateMod,{','.join(modHistory): 1},0,1,waitTimePredicted,[], selfTransitionTracker,lineIndex,durationTracker.copy(),limitedActionsTracker.copy(), currentRecordUpdate.copy(),recordHistory.copy())
        
        
        # if wannaPrint == 1:
        if lineIndex == 2 or lineIndex == 10:
            print(returnArray)
            # exit()
            # if timeCheckFinal == 0:
            # for toCheck in unsafeDoneTracker:
                # if not toCheck in individualAccuracyTracker[historyString]["AverageProbability"]:
                        # individualAccuracyTracker[historyString]["AverageProbability"][toCheck] = []
                # individualAccuracyTracker[historyString]["AverageProbability"][toCheck].append([lineIndex,0])
            # continue
        total = 0
        predictionsTracker += 1
        
        predictedState = returnArray[1]
        unsafePredictions = returnArray[0]
        
        tempDict = {}
        totalProb = 0
        unsafeDoneTrackerHere = {}
        for unsafeElem in unsafeDoneTracker:
            unsafeDoneTracker[unsafeElem] = 0
            unsafeDoneTrackerHere[unsafeElem] = 0
        timeCheckFinal = 1
        if timeCheckFinal == 1:
            for predictionName in unsafePredictions:
                actualCause = predictionName.replace('<','').replace('>','')
                #for actualCause in unsafeStateTypeTracker[predictionName.replace('<','').replace('>','')]:

                if not actualCause in tempDict:
                    tempDict[actualCause] = []
                tempDict[actualCause].append(unsafePredictions[predictionName])

                totalProb += unsafePredictions[predictionName]
            predictedViolations = []
            
            for predictionName in tempDict:   
                unsafeDoneTracker[predictionName] = 0
                unsafeDoneTrackerHere[predictionName] = 1
                totalPrediction = 0

                for individualElem in tempDict[predictionName]:
                    totalPrediction += individualElem
                if not predictionName in individualAccuracyTracker[historyString]["AverageProbability"]:
                    individualAccuracyTracker[historyString]["AverageProbability"][predictionName] = []
                individualAccuracyTracker[historyString]["AverageProbability"][predictionName].append([lineIndex,totalPrediction])
                if totalPrediction > unsafeStateThreshold:
                 predictedViolations.append([predictionName,1,totalPrediction])
                else:
                 predictedViolations.append([predictionName,0,totalPrediction])
                if predictionName in unseenTransitionsNotUnsafe and lastState.split('-')[1] in unseenTransitionsNotUnsafe[predictionName]:
                            unseenTransitionsNotUnsafe[predictionName][0].append(totalPrediction)
            averageQueryTime.append(time.time() - startTime)
            for unsafeValue in unsafeDoneTrackerHere:
                if unsafeDoneTrackerHere[unsafeValue] == 0:
                    if not unsafeValue in individualAccuracyTracker[historyString]["AverageProbability"]:
                        individualAccuracyTracker[historyString]["AverageProbability"][unsafeValue] = []
                    individualAccuracyTracker[historyString]["AverageProbability"][unsafeValue].append([lineIndex,0])

        if predictedState == 1:
            predictedCount += 1
        else:
            notPredictedCount += 1
        if lineIndex > order and lastState != None and (not currentStateTimeless.split('-')[1] in unsafeStates or (currentStateTimeless.split('-')[1] in unsafeStates and not checkIfUnsafeTime(evalList[lineIndex].replace('\n','').split('~')[1].split('-')[1] + '-' + evalList[lineIndex].replace('\n','').split('~')[1].split('-')[2] ,durationTracker,lineIndex))):
            unsafeOccuredHere = 0
            unsafeOccuredHereList = []

            limitedTemp = limitedActionsTracker.copy()
            limitedTempViolations = []
            checkStatePrior = currentState
            
            for i in range(timeSteps):
                #print(i + lineIndex)
                
                checkStateOrig = evalList[i+lineIndex+1].replace('\n','').split('~')[1]
                checkSplit = evalList[i+lineIndex+1].replace('\n','').split('~')[1].split('-')
                #checkState = checkSplit[0] + '-' + checkSplit[1]
                checkState = checkSplit[1]
                if checkState in relevantActionsTracker:
                    for combo in relevantActionsTracker[checkState]:
                        if len(limitedTemp[combo][2]) > limitedTemp[combo][0]:
                            deleted = 0
                            for arrayIndex in range(len(limitedTemp[combo][2])):
                                if lineIndex - limitedTemp[combo][2][arrayIndex-deleted] > limitedTemp[combo][1]:
                                    del limitedTemp[combo][2][arrayIndex-deleted]
                                    deleted += 1
                        limitedTemp[combo][2].append(lineIndex)
                        if len(limitedTemp[combo][2]) > limitedTemp[combo][0] and not combo in limitedTempViolations:
                            limitedTempViolations.append(combo)
                            probabilityAccuracy[combo]["PredictionDone"] = 1
                            if not checkState in individualAccuracyTracker[historyString]["Positive"]:
                                individualAccuracyTracker[historyString]["Positive"][checkState] = 0
                            individualAccuracyTracker[historyString]["Positive"][combo] += 1
                            probabilityAccuracy[combo]["Positive"] += 1
                            thereIsPositive = 1

                if checkState in unsafeStates and checkIfUnsafeTime(evalList[i+lineIndex+1].replace('\n','').split('~')[1].split('-')[1] + '-' + evalList[i+lineIndex+1].replace('\n','').split('~')[1].split('-')[2],durationTracker,lineIndex):
                    unsafeOccuredHere = 1
                    unsafeOccured += 1
                    currentPassed = 0
                    if i != timeSteps - 1:
                      for thingToDelete in individualAccuracyTracker[historyString]["AverageProbability"]:
                        
                        del individualAccuracyTracker[historyString]["AverageProbability"][thingToDelete][-1]
                      break
                    #print(lineIndex)
                    #print(currentStateMod)
                    highest = 0
                    highestState = -1
                    #if not probabilityAccuracy[checkState]["PredictionDone"] == 1:
                    for actualCause in unsafeStateTypeTracker[checkState]:
                        if not unsafeDoneTracker[actualCause] == 1:

                            unsafeDoneTracker[actualCause] =  1
                            #probabilityAccuracy[checkState]["PredictionDone"] = 1
                            #probabilityAccuracy[checkState]["Positive"] += 1'
                            if not actualCause in individualAccuracyTracker[historyString]["Positive"]:

                                individualAccuracyTracker[historyString]["Positive"][actualCause] = 0
                            unsafeOccuredHereList.append(actualCause)
                            individualAccuracyTracker[historyString]["Positive"][actualCause] += 1
                           

                            thereIsPositive = 1
                    checkStatePrior = checkState
            print(unsafeOccuredHereList)
            if len(unsafeOccuredHereList) > 0:
                #returnArray = explore_path(currentStateMod,{','.join(modHistory): 1},0,1,waitTimePredicted,[], selfTransitionTracker,lineIndex,durationTracker.copy(),limitedActionsTracker.copy(), currentRecordUpdate.copy(),currentStateRecord.copy())
                total = 0
                predictedState = returnArray[1]
                unsafePredictions = returnArray[0]
                
                tempDict = {}
                totalProb = 0
                predictedViolationsHere = []
                for predictionName in unsafePredictions:
                   
                    if unsafePredictions[predictionName] == 0:
                        continue
                    actualCause = predictionName.replace('<','').replace('>','')
                    #for actualCause in unsafeStateTypeTracker[predictionName.replace('<','').replace('>','')]:
                    if not actualCause in tempDict:
                        tempDict[actualCause] = []
                    tempDict[actualCause].append(unsafePredictions[predictionName])

                    totalProb += unsafePredictions[predictionName]
                predictedViolations = []

                for predictionName in tempDict:   
                    unsafeDoneTracker[predictionName] = 0
                    totalPrediction = 0

                    for individualElem in tempDict[predictionName]:
                        totalPrediction += individualElem
                    

                    predictedViolationsHere.append([predictionName,1,totalPrediction])

                for unsafeOccurred in unsafeOccuredHereList:
                     found = 0
                     for predictedViolationName in predictedViolationsHere:
                        
                        if predictedViolationName[0] == unsafeOccurred:
                            found = 1

                            if not unsafeOccurred in lowestThreshold:
                                lowestThreshold[unsafeOccurred] = [[predictedViolationName[2]],[lineIndex]]
                            elif len(lowestThreshold[unsafeOccurred][0]) < 4000 or predictedViolationName[2] < lowestThreshold[unsafeOccurred][0][-1]:
                                if len(lowestThreshold[unsafeOccurred][0]) == 4000:
                                    del lowestThreshold[unsafeOccurred][0][-1]
                                foundHere = 0
                                for search in range(len(lowestThreshold[unsafeOccurred][0])):

                                    if predictedViolationName[2] < lowestThreshold[unsafeOccurred][0][search]:
                                        lowestThreshold[unsafeOccurred][0].insert(search,predictedViolationName[2])
                                        foundHere = 1
                                        break
                                if foundHere == 0:
                                    lowestThreshold[unsafeOccurred][0] .append(predictedViolationName[2])
                            lowestThreshold[unsafeOccurred][1].append(lineIndex)
                     if found == 0:
                        if not unsafeOccurred in lowestThreshold:
                            lowestThreshold[unsafeOccurred] = [[0],[lineIndex]]
                        elif lowestThreshold[unsafeOccurred][0][0] != 0:
                            lowestThreshold[unsafeOccurred][0].insert(0,0)
                            lowestThreshold[unsafeOccurred][1].append(lineIndex)

            waitTimePredicted = 0
            del limitedTemp
            del limitedTempViolations

        totalProb = 0
    

    lastState = currentStateTimeless

averageProbabilityDifference = []
averageProbabilityDifferenceSeen = []
averageProbabilityDifferenceUnseen = []
averagePredictedProbabilityUnseen = []
averageProbabilityUnseen = []
averageUnseenPredictions = []
averageProbabilityDifProportional = []
averageProbabilityDifProportionalUnseen = []
averageProbabilityDifProportionalSeen = []

averageSeenProbability = []
averageUnseenProbability = []
averageSeenPrediction = []
averageUnseenPrediction = []

averageProbabilityDifference2 = []
averageProbabilityDifferenceSeen2 = []
averageProbabilityDifferenceUnseen2 = []
averageProbabilityDifProportional2 = []
averageProbabilityDifProportionalUnseen2 = []
averageProbabilityDifProportionalSeen2 = []


# averageProbabilityDifference = [0,0]
# averageProbabilityDifferenceSeen = [0,0]
# averageProbabilityDifferenceUnseen = [0,0]
# averagePredictedProbabilityUnseen = [0,0]
# averageProbabilityUnseen = [0,0]
# averageUnseenPredictions = [0,0]
# averageProbabilityDifProportional = [0,0]
positivesArray = []
probabilityArray = []
predictionsArray = []
averageDicString = ""
truePositivesSeen = 0
trueNegativesSeen = 0
falsePositivesSeen = 0
falseNegativesSeen = 0
truePositivesUnseen = 0
trueNegativesUnseen = 0
falsePositivesUnseen = 0
falseNegativesUnseen = 0
tpa = 0
tna = 0
fpa = 0
fna = 0
#print(lowestThreshold)
avgCalculator = []
tempUnseen = ''
tempUnseen = unseenStatesMain
# for historyStringHere in individualAccuracyTracker:
 #print(historyStringHere)
# with open("/home/man5336/Documents/ProvPredictor/EvalFolder/lowestThreshold.txt", "rb") as myFile:
            # lowestThreshold = pickle.load(myFile)
# with open("/home/man5336/Documents/ProvPredictor/EvalFolder/individualAccuracyTracker.txt", "rb") as myFile:
            # individualAccuracyTracker = pickle.load(myFile)
 #for predIndex, predictionChecker in enumerate(individualAccuracyTracker[historyStringHere]["AccuracyTracker"]):
 # for predIndex, predictionChecker in enumerate(individualAccuracyTracker[historyStringHere]["AverageProbability"]):
    # for accuracyTracker, accuracyElement in enumerate(individualAccuracyTracker[historyStringHere]["AverageProbability"][tempUnseen]):
        # avgCalculator.append(accuracyElement[0])
#calcAvg = statistics.mean(avgCalculator)
# for elemHere in lowestThreshold:
    # print(elemHere)
    # print(lowestThreshold[elemHere])
    # print()
with open("/home/man5336/Documents/ProvPredictor/EvalFolder/lowestThreshold.txt", "wb") as myFile:
            pickle.dump(lowestThreshold, myFile)
with open("/home/man5336/Documents/ProvPredictor/EvalFolder/individualAccuracyTracker.txt", "wb") as myFile:
            pickle.dump(individualAccuracyTracker, myFile)
print(lowestThreshold)
for predictionChecker in unsafeDoneTracker:
 bestFScore = [0,-1,-1,-1,-1]
 if not predictionChecker in lowestThreshold:
    continue
 #print(lowestThreshold[predictionChecker][0])
 for currentThresholdIndex, currentThreshold in enumerate(lowestThreshold[predictionChecker][0]):
  # if predictionChecker == '1':#and currentThresholdIndex == 0:
    # print(currentThreshold)
  falsePositives = 0
  truePositives = 0
  trueNegatives = 0
  falseNegatives = 0
  falsPosTrack = []
  for historyStringIndex, historyStringHere in enumerate(individualAccuracyTracker):
        for accuracyTracker, accuracyElement in enumerate(individualAccuracyTracker[historyStringHere]["AverageProbability"][predictionChecker]):
                
            if accuracyElement[1] >= currentThreshold:
                if not accuracyElement[0] in lowestThreshold[predictionChecker][1]:
                    if  not accuracyElement[1] >= (currentThreshold + (currentThreshold*0.5)): 
                        continue
                    #print(accuracyElement)
                    falsePositives += 1
                    # if predictionChecker == '1':
                        # print(accuracyElement[1])
                        
                        # falsPosTrack.append(accuracyElement[0] )
                else:

                    truePositives += 1


            else:
                if  accuracyElement[0] in lowestThreshold[predictionChecker][1]: 
                    falseNegatives += 1
                else:
                    trueNegatives += 1

  
  precision = truePositives/ (truePositives + falsePositives)
  recall = truePositives/ (truePositives + falseNegatives)
  fscore1 = (2 * (precision * recall))
  fscore = fscore1/(precision + recall)

      # exit()
  if fscore > bestFScore[0]:
    bestFScore = [fscore,truePositives,trueNegatives,falsePositives,falseNegatives]

 if predictionChecker == unseenStatesMain:
    # truePositivesUnseen += truePositives
    # trueNegativesUnseen += trueNegatives
    # falsePositivesUnseen += falsePositives
    # falseNegativesUnseen += 0
    truePositivesUnseen += bestFScore[1]
    trueNegativesUnseen += bestFScore[2]
    falsePositivesUnseen += bestFScore[3]
    falseNegativesUnseen += bestFScore[4]
 else:
    # truePositivesSeen += truePositives
    # trueNegativesSeen += trueNegatives
    # falsePositivesSeen += falsePositives
    # falseNegativesSeen += 0
    truePositivesSeen += bestFScore[1]
    trueNegativesSeen += bestFScore[2]
    falsePositivesSeen += bestFScore[3]
    falseNegativesSeen += bestFScore[4]
        
 
if len(averageProbabilityDifference) == 0:
    averageProbabilityDifference = [0]
    
if len(averageProbabilityDifferenceUnseen) == 0:
    averageProbabilityDifferenceUnseen = [0]
    averageUnseenProbability = [0]
    averageUnseenPrediction = [0]
    
    
if len(averageProbabilityDifferenceSeen) == 0:
    averageProbabilityDifferenceSeen = [0]
    averageSeenProbability = [0]
    averageSeenPrediction = [0]
    
    

with open("/home/man5336/Documents/ProvPredictor/EvalFolder/storageOverheadExperimentCombinedHistory.csv", 'a') as output_file:
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/QueryLatencyFarmNew.csv", 'a') as output_file2:
        with open("/home/man5336/Documents/ProvPredictor/EvalFolder/effectivenessTestingFarmNew.csv", 'a') as output_file3:

            #reportString = str(trainingSize) + "," + str(order) + "," + str(timeSteps) + "," + str(timeStepLength) + "," + str(unsafeStateThreshold) + "," +   str(historyGroupSize)  + "," + str(minimumProabilityFactor ) + "," + str(historyDiffLimit) + "," + str(unsafeStateNum)
            #reportString = str(policyNum) + "," + str(stateNum) + "," + str(depthSize) + "," + str(durations) + "," + str(version)
            reportString = str(trainingSize) + ',' + str(timeSteps) + "," + str(unsafeStateThreshold) + ','  +str(durations) + ',' + str(version) + ',' + str(unseenStatesMain)
            
            
            reportString2 = reportString + "," + str(statistics.mean(averageQueryTime)) + "," + str(averageQueryTime[0]) + "," + str(averageQueryTime[-1]) + '\n'
            #reportString3 = reportString + "," + str(sys.getsizeof(transitionDict)) + ":" + str(sys.getsizeof(unsafeStates)) + ":" + str(sys.getsizeof(bucketsTime)) + ":" + str(sys.getsizeof(bucketsContext)) + ":" + str(sys.getsizeof(bw)) + ":" + str(sys.getsizeof(validPathsForHistory))
            # if len(averageProbabilityDifference) > 0:
                # reportString = reportString + "," + str(unsafeStateAccuracy["True Positives"]) + ":" + str(unsafeStateAccuracy["False Positives"])  + "," + str(statistics.mean(averageProbabilityDifference)) + ','  + str(statistics.mean(averageProbabilityDifProportional)) #averageDicString
            # else:    
                # reportString = reportString + "," + str(unsafeStateAccuracy["True Positives"]) + ":" + str(unsafeStateAccuracy["False Positives"])  + "," + str(0) + ',' + str(0)
            if trainingSize != 0:
             
                reportString = reportString + ',' + str(truePositivesSeen) + ',' + str(trueNegativesSeen) + ',' + str(falsePositivesSeen) + ',' + str(falseNegativesSeen) + ',' + str(truePositivesUnseen) + ',' + str(trueNegativesUnseen) + ',' + str(falsePositivesUnseen) + ',' + str(falseNegativesUnseen)
            else:
                reportString = reportString + ',' + str(averageProbabilityDifference) + ',' + str(thereIsPositive)
            #for thingHere in lowestThreshold:
            #    reportString = reportString + ','  + str(thingHere) + ',' + str(lowestThreshold[thingHere][0])
            reportString = reportString + "\n"
            #reportString2 = reportString2 + "\n"
            #reportString3 = reportString3 + "\n"
            #output_file.write(reportString3)
            output_file2.write(reportString2)
            output_file3.write(reportString)

            #for unsafeStateToCheck in unsafeStateAccuracyChecker:
                   #stringWrite = str(unsafeStateToCheck) + ',' + str(unsafeStateAccuracyChecker[unsafeStateToCheck]) + ',' + str(unsafeStateAccuracyChecker2[unsafeStateToCheck]) + '\n'
                   #output_file3.write(stringWrite)
exit()    
    # for flavor in FLAVORS:
        # with open('/home/mike/Documents/helion/results/randomTraining.csv','w') as toFile:
            # with open(input_file,'r',encoding="utf-8-sig") as fromFile:
                # if "random" in trainingSplit[-1]:
                    # iterable = range(trainingSize)
                # else:
                    # iterable = fromFile
                # #for line in range(PREDICTION_LENGTH):
                # for line in iterable:
                    # if "random" in trainingSplit[-1]:
                        # historyState = random.randint(1,highestState)
                        # history = ["<" + str(historyState) + ">"]
                        # #history = ["<10>"]
                    # else:
                        # history = line.split()
                    # if line % 100 == 0:
                        # print(line)
                    # #historyState = random.randint(0,highestState)
                    
                    # #history = ["<" + str(historyState) + ">"]
                    # # Create Input
                    # construct_model(flavor,history)    
                    # #print(line)
                    # #print(history)
                    # # Train the model
                    # #run_server(training_file,order,vocab_file)

                    # # Construct INPUT FOR MODEL
                    # output_json = make_request()
                    # to_write = str(history).replace('[','').replace(']','').replace('<','').replace('>','').replace('\'','') + ',' + str(output_json["stream"]).replace('[','').replace(']','').replace('<','').replace('>','').replace('\'','') + '\n'
                    
                    # while "/s" in to_write:
                        # output_json = make_request()
                        # to_write = str(history).replace('[','').replace(']','').replace('<','').replace('>','').replace('\'','') + ',' + str(output_json["stream"]).replace('[','').replace(']','').replace('<','').replace('>','').replace('\'','') + '\n'
                    # toFile.write(to_write)

            