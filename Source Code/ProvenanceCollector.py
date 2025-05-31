import csv
import os
import time
import json
import random as rm
import numpy as np
import sys
import collections
import calendar
import datetime
import re
import difflib
import copy
import unicodedata
import string
import subprocess
import pickle
import statistics
from scipy.stats import chi2
from collections import defaultdict
from copy import deepcopy
import pandas as pd
from statsmodels.tsa.stattools import grangercausalitytests
import random
from contextlib import contextmanager,redirect_stderr,redirect_stdout
from os import devnull

@contextmanager
def suppress_stdout_stderr():
    """A context manager that redirects stdout and stderr to devnull"""
    with open(devnull, 'w') as fnull:
        with redirect_stderr(fnull) as err, redirect_stdout(fnull) as out:
            yield (err, out)




#A service object representing each service in the user's system, containing the current state and all known trigger, query, and action information, elements is a list of dictionaries for triggers,queries,and actions in that order
class Service(object):
    def __init__(self, state):
        self.elements = [{},{},{},[]]
        self.state = state
        self.stateExtractions = []

#Objects for storing all known information about triggers, queries, and actions        
class Trigger(object):
    def __init__(self):
        self.fields = {}
        self.ingredients = {}
        self.occurances = 1
        
class Query(object):
    def __init__(self):
        self.fields = {}
        self.ingredients = {}
        self.occurances = 1

        
class Action(object):
    def __init__(self):
        self.fields = {}
        self.occurances = 1

currentTime = 0
currentStateTime = 0
currentStateTimeVar = None
eventTime = None
pendingActions = {}

stateHistorySimple = []
stateHistorySimpleRecord = []
simpleUnsafeStates = {}
simpleDurationsTracker = {}
simpleTimeTracker = {}
otherServiceStateCalc = []
unsafeDurationTracker = {}
stateExtractionsContextDict = []

limitedActionList = {}

transitionList = {}
validTargetsList = {}
transitionsOccured = {}

stateList = {}
stateOccured = {}


#Global list of all known services 
services = {}


def chiSquareTimeWindow(linksCheck,lag,dataList):
    global state
    linksFound = []
    changesViewed = []
    #dataFile = open(sys.argv[1], "r")
    #dataList = list(dataFile)
    line = dataList[0]
    deviceNames = line.split(",")
    deviceNames[len(deviceNames) - 1] = deviceNames[len(deviceNames) - 1][:-1]
    valueRecord = {}
    pollsForValue = {}
    possibleStates = {}
    basicStateTracker = []
    for index, name in enumerate(deviceNames):
        valueRecord[index] = {}
        pollsForValue[index] = {}
        possibleStates[index] = []
        basicStateTracker.append({})
        
    highCorrelationPairs = []
    totalLines = 0

    for index in range(len(dataList) - lag - 1):
        line = dataList[index+1]
        #if index != 0 and dataList[index] == line:
        #    continue
        deviceValues = line.split(",")
        deviceValues[len(deviceValues) - 1] = deviceValues[len(deviceValues) - 1][:-1]
        changedTracker = [[] for k in range(len(deviceNames))]
        totalLines+=1
        for valueIndex, tempValue in enumerate(deviceValues):
            if not tempValue in basicStateTracker[valueIndex]:
                basicStateTracker[valueIndex][tempValue] = 0
            basicStateTracker[valueIndex][tempValue] += 1
        # for device1Index, device1Val in enumerate(deviceValues):
            # if not device1Val in pollsForValue[device1Index]:
                # pollsForValue[device1Index][device1Val] = 0
            # pollsForValue[device1Index][device1Val] += 1
        #changedAtAll = 0
        for exploreIndex in range(lag):
            newLine = dataList[index + 2 + exploreIndex]

            if line == newLine:
                continue
            
            

            
            newDeviceValues = newLine.split(",")
            newDeviceValues[len(deviceValues) - 1] = newDeviceValues[len(deviceValues) - 1][:-1]
            for device1Index, device1Val in enumerate(deviceValues):
                #if not device1Val in possibleStates[device1Index]:
                #    possibleStates[device1Index].append(device1Val)
                found = 0
                
                
                
                # print(deviceValues[device1Index] != newDeviceValues[device1Index])
                # print(not newDeviceValues[device1Index] in changedTracker[device1Index])
                
                
                
                if deviceValues[device1Index] != newDeviceValues[device1Index] and not newDeviceValues[device1Index] in changedTracker[device1Index]:
                    #changedAtAll = 1
                    changedTracker[device1Index].append(newDeviceValues[device1Index])
                    for record in valueRecord:
                        # if record == device1Index:
                            # continue
                        
                        if not device1Index in valueRecord[record]:
                            valueRecord[record][device1Index] = {}
                        if not newDeviceValues[device1Index] in valueRecord[record][device1Index]:
                            valueRecord[record][device1Index][newDeviceValues[device1Index]] = [0,{}]
                        valueRecord[record][device1Index][newDeviceValues[device1Index]][0] += 1
                        if not deviceValues[record] in valueRecord[record][device1Index][newDeviceValues[device1Index]][1]:
                            valueRecord[record][device1Index][newDeviceValues[device1Index]][1][deviceValues[record]] = 0
                        valueRecord[record][device1Index][newDeviceValues[device1Index]][1][deviceValues[record]] += 1
                    #This implementation looks backwards
                    # changedTracker[device1Index].append(newDeviceValues[device1Index])
                    # for record in valueRecord:
                        # if record == device1Index:
                            # continue
                        # if not newDeviceValues[device1Index] in pollsForValue[record]:
                            # pollsForValue[record][newDeviceValues[device1Index]] = 0
                        # pollsForValue[record][newDeviceValues[device1Index]] += 1
                        # if not deviceValues[record] in valueRecord[record]:
                            # valueRecord[record][deviceValues[record]] = {}
                        # if not device1Index in valueRecord[record][deviceValues[record]]:
                            # valueRecord[record][deviceValues[record]][device1Index] = {}
                        # if not newDeviceValues[device1Index] in valueRecord[record][deviceValues[record]][device1Index]:
                            # valueRecord[record][deviceValues[record]][device1Index][newDeviceValues[device1Index]] = 0
                        # valueRecord[record][deviceValues[record]][device1Index][newDeviceValues[device1Index]] += 1
            #exit()
    finalResults = {}
    for linkToCheck in linksCheck:
        
            
        #for targetIndex, targetState in enumerate(state[deviceNames[linkToCheck]["stateExtractions"]]):
            for causalDevice in linksCheck[linkToCheck][0]:
                # if causalDevice == linkToCheck:
                    # if linkToCheck == 4:
                        # print(state[deviceNames[int(linkToCheck)]]["stateExtractions"])
                    # for causedState, stateProxy in enumerate(state[deviceNames[int(linkToCheck)]]["stateExtractions"]):
                        # if causedState == '-1':
                            # continue
                        # if not state[deviceNames[linkToCheck]]["stateExtractions"][int(causedState)] in finalResults:
                            # finalResults[state[deviceNames[linkToCheck]]["stateExtractions"][int(causedState)]] = {}
                        # for causalState, proxyTwo in enumerate(state[deviceNames[int(linkToCheck)]]["stateExtractions"]): 
                            # if causalState == '-1':
                                # continue
                            # if not str(causalDevice) in finalResults[state[deviceNames[linkToCheck]]["stateExtractions"][int(causedState)]]:
                                # finalResults[state[deviceNames[linkToCheck]]["stateExtractions"][int(causedState)]][str(causalDevice)] = []
                            # finalResults[state[deviceNames[linkToCheck]]["stateExtractions"][int(causedState)]][str(causalDevice)].append(str(causalState))
                    # continue
                for causedState in valueRecord[causalDevice][linkToCheck]:
                   if causedState == '-1':
                       continue
                   if not state[deviceNames[linkToCheck]]["stateExtractions"][int(causedState)] in finalResults:
                    finalResults[state[deviceNames[linkToCheck]]["stateExtractions"][int(causedState)]] = {}

                   for causalState in valueRecord[causalDevice][linkToCheck][causedState][1]: 
                    if causalState == '-1':
                       continue
                    if causalDevice == linkToCheck and causedState == causalState:
                        continue
                    
                    expectedValue = (basicStateTracker[causalDevice][causalState]*valueRecord[causalDevice][linkToCheck][causedState][0])/totalLines
                    if expectedValue < 1: 
                        continue
                    
                    
                    
                    
                    
                    
                    #valueRecord[causalDevice][linkToCheck][causedState][0])*(1/len(valueRecord[causalDevice][linkToCheck][causedState][1])
                    chiValue = (abs(valueRecord[causalDevice][linkToCheck][causedState][1][causalState] - expectedValue)**2)/expectedValue
                    if state[deviceNames[linkToCheck]]["stateExtractions"][int(causedState)] == "soil_moist_2_weather:90.0":
                       print(causalDevice)
                       print(causalState)
                       print(chi2.pdf(chiValue,1) )
                       print()
                    if chi2.pdf(chiValue,1) <= 0.05:
                    #if valueRecord[causalDevice][linkToCheck][causedState][1][causalState]/valueRecord[causalDevice][linkToCheck][causedState][0] > 1/len(valueRecord[causalDevice][linkToCheck][causedState][1]):
                        #print("%s in %s causes %s in %s with likelihood %f" % (causalState,deviceNames[linkToCheck],causedState,deviceNames[causalDevice],valueRecord[linkToCheck][causalDevice][causedState][1][causalState]/valueRecord[linkToCheck][causalDevice][causedState][0]))
                        #if valueRecord[causalDevice][linkToCheck][causedState][1][causalState]/valueRecord[causalDevice][linkToCheck][causedState][0] < 1:
                            #newLink = expandCondition([causalState,linkToCheck,causedState,causalDevice],lag, valueRecord)
                            if not str(causalDevice) in finalResults[state[deviceNames[linkToCheck]]["stateExtractions"][int(causedState)]]:
                                finalResults[state[deviceNames[linkToCheck]]["stateExtractions"][int(causedState)]][str(causalDevice)] = []
                            finalResults[state[deviceNames[linkToCheck]]["stateExtractions"][int(causedState)]][str(causalDevice)].append(str(causalState))
                            
                            
                            
    #print(finalResults)
    return finalResults
                #print("%s in %d causes %s in %d with likelihood %f" % (causalState,linkToCheck,causedState,linkToCheck[1],valueRecord[linkToCheck][linkToCheck[1]][causedState][1][causalState]/valueRecord[linkToCheck][linkToCheck[1]][causedState][0]))
                

#List of states implied by different types of events,fields, and ingredients
impliedStates = []

#Unsafe state definitions, in the form of a list for each service relevant to the unsafe state [["ServiceName",["StateValue"],["Field:Values"],["IngredientValues"],["Time"]]] where:
#ServiceName and StateValue are mandatory, the rest are optional, but leave empty lists if you skip optional arguments
#ServiceName is the name of the service as given in rule definitions (E.g: MagicHue)
#StateValue is the state the service must be in for the unsafe state to be present (E.g: On)
    #Note: State can also be provided as a list of valid values (E.g: On+Off) and a range (E.g: 60-70)
#Field:Values is a list of any fields relevant to the unsafe state in the form Fieldname:Fieldvalue (E.g:WhichLights:LivingRoom)
    #Note: Value can also be provided as a list of valid values (E.g: 60+61+62) and a range (E.g: 60-70)
#Ingredient:Values is a list of any ingredients relevant to the unsafe state in the form Ingredientname:Ingredientvalue (E.g:File:MyFile)
    #Note: Value can also be provided as a list of valid values (E.g: Off+Offline) and a range (E.g: 60-70)
#Time is a single time or range where the unsafe state must occur to be unsafe, in the form ["Month","Day","Weekday","hour:minute"], which can also be represented in ranges by ["Month-Month","Day-Day","Weekday-Weekday","hour:minute-hour:minute"]
    #Note: If any element is irrelevant to unsafe state, leave in empty quotes ("")
    #Example: ["May","2-24","Mon-Fri","12:00"]
#Current unsafe states are: Lights on when user is asleep, heater on when temperature is too hot, heater on when temperature is too cold, user is spammed with excessive SMS messages, location data is leaked, financial data is leaked, unwanted donations
unsafeStates = {}

#Limited actions are those that should not occur more than a defined number of times within a set time frame in the form ["ServiceName","EventName",Limit,TimeFrame]
#ServiceName is the name of the service as given in rule definitions (E.g: MagicHue)
#EventName is the name of the event as given in rule definitions (E.g: TurnOnLight)
#Limit is a numeric value of the maximum number of times the event should occur within the time frame
#TimeFrame is a numerical value representing the time frame in minutes
limitedActions = {}

#Secure information identifies information that should not be leaked to unsecure surfaces in the form ["ServiceName","EventName",["Fields"],["Ingredients"],"Whitelist/Blacklist",["ServicesList"],DataRequired:0/1], which defines either a trigger or query
#ServiceName is the name of a service as given in rule definitions (E.g: MagicHue) which the information should not be leaked from
#EventName is the name of a service event as given in rule definitions (E.g: TurnOnLight) that indicates this is the event no data should be leaked from, leave as "" if any event from the service is secure
#["Fields"] is a list of field names and values (E.g:WhichLights:LivingRoom) which specify the information is secure if the event's fields match these values
    #Note: Value can also be provided as a list of valid values (E.g: 60+61+62) and a range (E.g: 60-70)
#["Ingredients"] is a list of ingredient names (E.g:CreatedAt) which specify the information is secure if the event's ingredients match these values
    #Note: Value can also be provided as a list of valid values (E.g: 60+61+62) and a range (E.g: 60-70)
#Whitelist/Blacklist is a string either whitelist or blacklist which determines if unsafe sinks are identified by a whitelist of allowed services or blacklist of non-allowed services
#ServicesList is a list of services that make up the whitelist or the blacklist
#DataRequired is an integer 0 or 1 that specifies if leaks should only be counted if a service uses an ingredient, 0 for no and 1 for yes
secureInformation = []

#Used for converting months to numbers for analysis
months = ["filler","jan","feb","mar","apr","may","jun","jul","aug","sep","oct","nov","dec"]
weekdays = ["sun","mon","tue","wed","thu","fri","sat"]

#A list of events parsed into a dict structure
structuredEvents = []

#A stored image of the current system state
#state = {"MagicHue":{"state":"On","fields":{"WhichLights":"LivingRoom"},"ingredients":{"TestIngredient":"Ingredient"}},"Time":datetime.datetime(2021,3,22,22,30)}
#An optional initial state can be given in the input file by adding a first line "InitialState" and a series of lines defining the initial states of each service in the following form, ended with "InitialStateEnd" line
#Lines should be of the form "{ServiceName}/{ServiceState}/{Field1:Field1Value-Field2:Field2Value...}/{Ingredient1:Ingredient1Value-...}"
state = {}
initialStateData = []

#For tracking state probability of occurance
stateOccurances = []

#List of words that imply a viable state in a given service for automatic service extraction, list with each element in the form ["implyingWord","implyingState"]
stateExtractionHeuristics = [["on","On"],["off","Off"],["connected","Connected"],["disconnected","Disconnected"],["exit","Not at"],["enter","Located At"],["temperature","Temp At"]]

#Track all states that occured in the system
stateHistory = []

#List of unsafeStates that occured during run
unsafeStateList = []

#Function for gathering user-defined or automatically detected unsafe states
#Currently simply generates our sample unsafe states
def assignUnsafeStates():
     
    
    with open("policiesFarm.csv",'r') as policies_file:
        testList = list(policies_file)
        stateID = 0
        for line in testList:
            line= line.replace('\n','')
            typeCheck = line.split(':')[0]
            remainingLine = line[len(typeCheck)+1:]
            if typeCheck  == "state":
                policyBreakdown = {}
                label = 0
                openings = []
                timeBounds = []
                relevantDuration = 0
                for index, letter in enumerate(remainingLine):
                    if letter  == '(':
                        policyBreakdown[str(label)] = [[],index,""]
                        openings.append(str(label))
                        label += 1
                    elif letter == ')':
                        contentElems = remainingLine[policyBreakdown[openings[-1]][1]+1:index].split(',')
                        duration = None

                        logicType = contentElems[-1]
                        del contentElems[-1]
                        use = 1
                        for elem in contentElems:
                            if '(' == elem[0]: 
                                use = 0
                            if use == 1:
                                if elem[-1] != '"':
                                    relevantDuration = 1
                                    durationSplit = elem.split('"')[-1].split(':')
                                    duration = datetime.timedelta(days=int(durationSplit[0]),hours=int(durationSplit[1]),minutes=int(durationSplit[2]),seconds=int(durationSplit[3]))
                                    elem = elem[:elem.rfind('"')+1]
                                notTrue = 0
                                if elem[0:3] == "NOT":
                                    elem = elem[3:]
                                    notTrue = 1
                                elemSplit = elem.split('-')
                                if len(elemSplit) > 2:
                                    elem1 = ""
                                    elem2 = ""
                                    secondElem = 0
                                    for elemPart in elemSplit:
                                        if secondElem == 0:
                                            elem1 += elemPart
                                            if elemPart[-1] == '\"':
                                                secondElem = 1
                                            else:
                                                elem1 += "-"
                                        else:
                                            elem2 += elemPart
                                            if elemPart[-1] != '\"':
                                                elem2 += "-"
                                    elemSplit = [elem1[1:-1],elem2[1:-1],duration]
                                else:
                                    elemSplit = [elemSplit[0][1:-1],elemSplit[1][1:-1],duration]
                                if notTrue == 1:
                                    elemSplit.append("NOT")    
                                if elemSplit[0] == "Time":
                                    if '-' in elemSplit[1]:
                                        startTime = datetime.datetime(year=2000,month=6,day=20,hour=int(elemSplit[1].split('-')[0].split(':')[0]),minute=int(elemSplit[1].split('-')[0].split(':')[1]))
                                        endTime = datetime.datetime(year=2000,month=6,day=20,hour=int(elemSplit[1].split('-')[1].split(':')[0]),minute=int(elemSplit[1].split('-')[1].split(':')[1]))
                                        #timeBounds.append([(startTime - datetime.timedelta(minutes=1)).time(),0])
                                        timeBounds.append([startTime,endTime])
                                        #timeBounds.append([(endTime + datetime.timedelta(minutes=1)).time(),0])
                                    else:
                                        timeBounds.append([datetime.datetime(year=2000,month=6,day=20,hour=int(elemSplit[1].split(':')[0]),minute=int(elemSplit[1].split(':')[1]))])
                                        #timeBounds.append([(datetime.time(year=2000,month=6,day=20,hour=int(elemSplit[1].split(':')[0]),minute=int(elemSplit[1].split(':')[1])) - datetime.timedelta(minutes=1)).time(),0])
                                policyBreakdown[openings[-1]][0].append(elemSplit.copy())
                                    
                            if ')' == elem[-1]:
                                use = 1
                        policyBreakdown[openings[-1]][-1] = logicType
                        policyBreakdown[openings[-1]].append(duration)
                        if len(openings) > 1:
                            policyBreakdown[openings[-2]][0].append(openings[-1])
                        del openings[-1]
                timeBounds.sort()
                policyBreakdown['0'][1] = timeBounds
                policyBreakdown["Duration"] = relevantDuration
                unsafeStates[stateID] = policyBreakdown.copy()
                stateID += 1
                #unsafeStates.append(policyBreakdown.copy())
            elif typeCheck == "limited":
                    remainingSplit = remainingLine.split(',')
                    if not remainingSplit[0] in limitedActions:
                        limitedActions[remainingSplit[0][1:-1]] = {}
                    timeSplit = remainingSplit[3].split(':')
                    secondsTime = int(timeSplit[0]) * 86400 + int(timeSplit[1]) * 3600 + int(timeSplit[2]) * 60 + int(timeSplit[3])
                    limitedActions[remainingSplit[0][1:-1]][remainingSplit[1][1:-1]] = [secondsTime,int(remainingSplit[2])]
            else:
                remainingSplit = remainingLine.split(',')
                remainingSplit[3] = remainingSplit[3].replace('[','').replace(']','')
                secureInformation.append([remainingSplit[0],remainingSplit[1],remainingSplit[2],remainingSplit[3].split(',')])


    #Update once state is correctly tracked     
         
    #Unsafe states to prevent light being on when user is asleep
    #unsafeStates.append([["MagicHue","On",["WhichLights:LivingRoom"],[],["","","","0:00-6:00"]]])
    #unsafeStates.append([["MagicHue","On",["WhichLights:LivingRoom"],[],["","","","22:00-24:00"]]])
    
    #addUnsafeParameters
   
def defineState(event,element):
    global state,services
    #print("At define state")
    exit()

def createState():
    global state,services,initialStateData, limitedActions, stateHistorySimple, stateHistorySimpleRecord, stateExtractionsCurrentEvent, stateExtractionsContext, overallStateExtractions, stateList, stateOccured
    stateExtractionsCurrentEvent = []
    stateExtractionsContext = []
    overallStateExtractions = []
    
    #Implement automatic inference of true states of devices (e.g: on/off)
    # for service in services:
        # for trigger in services[service].elements[0]:
            # for event in services[service].elements[0][trigger]:
                # defineState(event, services[service].elements[0][trigger])  
    deviceNameString = ""
    initialStateString = ""
    for serviceIndex, service in enumerate(services):
        #state[service] = {"state":"Initial","fields":{},"ingredients":{}, "limitedData":{}, "stateExtractions": [], "simpleState": 0}
        state[service] = {"state":"Initial","fields":{},"ingredients":{}, "limitedData":{}, "stateExtractions": [], "simpleState": 0, "changesSimple": []}
    for stateIndex, stateName in enumerate(state):
        if stateIndex != 0:
            deviceNameString += ","
        deviceNameString += stateName
        if stateIndex != 0:
            initialStateString += ","
        initialStateString += '0'
        # if serviceIndex != 0:
            # initialStateString += ","
        # initialStateString += '0'
        
    with open("CausalFile.txt",'w') as causalFile:
        for initialStateIndex, initialState in enumerate(initialStateData):
            if not initialState[0] in state:
                continue
            if initialState != 0:
                causalFile.write(',')
            causalFile.write(initialState[0])
        causalFile.write('\n')
        
    
    
    
    for initialStateIndex, initialState in enumerate(initialStateData):
        if not initialState[0] in state:
            continue
        # stateDefined = str(initialState[1])
        # initialStateLimited = ""
        # if initialState[0] in limitedActions:
            # for limitedAction in limitedActions[initialState[0]]:
                # initialStateLimited = ",0"
                # if limitedAction in state[initialState[0]]["limitedData"]:
                
                    # state[initialState[0]]["limitedData"][limitedAction] = {}
                    # state[initialState[0]]["limitedData"][limitedAction]["limit"] = limitedActions[initialState[0]][limitedAction][0]
                    # state[initialState[0]]["limitedData"][limitedAction]["timeThreshhold"] = limitedActions[initialState[0]][limitedAction][1]
                    # state[initialState[0]]["limitedData"][limitedAction]["eventTracker"] = []
                # else:
                    # state[initialState[0]]["limitedData"] = {}
                    # state[initialState[0]]["limitedData"][limitedAction] = {}
                    # state[initialState[0]]["limitedData"][limitedAction]["limit"] = limitedActions[initialState[0]][limitedAction][0]
                    # state[initialState[0]]["limitedData"][limitedAction]["timeThreshhold"] = limitedActions[initialState[0]][limitedAction][1]
                    # state[initialState[0]]["limitedData"][limitedAction]["eventTracker"] = []
                # if limitedAction == initialState[1]:
                    # state[initialState[0]]["limitedData"][limitedAction]["eventTracker"].append(0)
                    # #stateDefined = stateDefined + ":1"
        stateList[initialState[0]] = []
        stateList[initialState[0]].append(initialState[1])
        stateOccured[initialState[0]] = 0
        state[initialState[0]]["state"] = initialState[1]
        #print(initialState[0])
        #print(initialState[1])
        
        
        #state[initialState[0]]["stateExtractions"].append(stateDefined)
        #state[initialState[0]]["simpleState"] = "0" + initialStateLimited 
        state[initialState[0]]["simpleState"] = initialState[0] + ":" + initialState[1]
        state[initialState[0]]["stateExtractions"].append(initialState[0] + ":" + initialState[1])
        if "-" in initialState[2]:
            fieldSplit = initialState[2].split("-")
        elif initialState[2] == "":
            fieldSplit = []
        else:
            fieldSplit = [initialState[2]]
        for field in fieldSplit:
            valueSplit = field.split(":",1)
            state[initialState[0]]["fields"][valueSplit[0]] = valueSplit[1]
        if "-" in initialState[3]:
            ingredientSplit = initialState[3].split("-")
        elif initialState[3] == "":
            ingredientSplit = []
        else:
            ingredientSplit = [initialState[3]]
        for ingredient in ingredientSplit:
            valueSplit = ingredient.split(":",1)
            state[initialState[0]]["ingredients"][valueSplit[0]] = valueSplit[1] 
    with open("traceOutput.csv", 'w') as trace_output:
        trace_output.write(deviceNameString + "\n")
        trace_output.write(initialStateString + "\n")
    # stateHistorySimple.append([0,"<0,>])
    # stateHistoryCalc = ""
    # for stateIndex, testState in enumerate(state):
        # if stateIndex != 0:
            # stateHistoryCalc += ":"
        # stateHistoryCalc += str((state[testState]["simpleState"]))
    # stateHistorySimpleRecord.append(stateHistoryCalc)

def updateState(event,causalFile):
    global state,stateOccurances,stateHistory, currentStateTime, unsafeStateList,stateHistorySimple,simpleUnsafeStates, currentStateTimeVar, stateExtractionsCurrentEvent, stateExtractionsContext, overallStateExtractions, limitedActionList
    global stateList, transitionList, validTargetsList, stateOccured, pendingActions
    stateUnsafe = 0
    # atLeastOne = 1
    # while atLeastOne == 1:
        # maxTime = event["Time"]
        # finishedActions = []
        # atLeastOne = 0
        # for pendingAction in pendingActions:
            # if pendingActions[pendingAction] < maxTime:
                # maxTime = pendingActions[pendingAction]
                # atLeastOne = 1
        # for pendingAction in pendingActions:
            # if pendingActions[pendingAction] <= maxTime:
                # finishedActions.append(pendingAction)
                # timeDifCalc = (event["Time"]-pendingActions[pendingAction])
                # currentTemp =  currentStateTime - (60 * int(str(timeDifCalc).split(':')[0])) + int(str(timeDifCalc).split(':')[1])
                # pendingActionSplit = pendingAction.split(':')
                # if not pendingActionSplit[0] in stateList:
                    # stateList[pendingActionSplit[0]] = []
                    # stateOccured[pendingActionSplit[0]] = []
                # if not pendingActionSplit[1] in stateList[pendingActionSplit[0]]:
                    # stateList[pendingActionSplit[0]].append(pendingActionSplit[1])
                # stateOccured[pendingActionSplit[0]] = currentTemp
                # state[pendingActionSplit[0]]["state"] = pendingActionSplit[1]
                # fieldsTotal = ""

                # actionName = pendingActionSplit[1]
         
                # stateDefined = pendingAction

                # state[pendingActionSplit[0]]["simpleState"] = stateDefined

                # if not stateDefined in state[pendingActionSplit[0]]['stateExtractions']:
                            # state[pendingActionSplit[0]]["stateExtractions"].append(stateDefined)
                # currentEventCalc = ""
                # otherServiceStateCalc = ""
                # otherServicesDicCalc = {}
                # for stateIndex, testState in enumerate(state):
                
                    # if not testState == pendingActionSplit[0]:
                        
                            
                        # if testState == "Time":
                            # continue
                        
                        # else:
                            # if otherServiceStateCalc != "":
                                # otherServiceStateCalc += ","
                            # otherServiceStateCalc += str((state[testState]["simpleState"]))
                            # otherServicesDicCalc[testState] = str((state[testState]["simpleState"])).split(':')[1]
                    # else:
                        # if currentEventCalc != "":
                            # currentEventCalc += ","
                        # currentEventCalc += str((state[testState]["simpleState"]))
                        # if otherServiceStateCalc != "":
                            # otherServiceStateCalc += ","
                        # otherServiceStateCalc += str((state[testState]["simpleState"]))
                        # otherServicesDicCalc[testState] = str((state[testState]["simpleState"])).split(':')[1]
                # if not currentEventCalc in stateExtractionsCurrentEvent:
                    # stateExtractionsCurrentEvent.append(currentEventCalc)
                # if not otherServiceStateCalc in stateExtractionsContext:
                    # stateExtractionsContext.append(otherServiceStateCalc)
                    # stateExtractionsContextDict.append(otherServicesDicCalc)
                # if len(stateHistorySimple) > 0:
                    # if not stateHistorySimple[-1][1].split('-')[1] in transitionList:
                        # transitionList[stateHistorySimple[-1][1].split('-')[1]] = {}
                        # validTargetsList[stateHistorySimple[-1][1].split('-')[1]] = []
                    # transitionList[stateHistorySimple[-1][1].split('-')[1]][str(stateExtractionsCurrentEvent.index(currentEventCalc))] = str(stateExtractionsContext.index(otherServiceStateCalc))
                    # transitionList[stateHistorySimple[-1][1].split('-')[1]][str(stateExtractionsContext.index(otherServiceStateCalc)) + '-c'] = str(stateExtractionsCurrentEvent.index(currentEventCalc))
                    # if not str(stateExtractionsContext.index(otherServiceStateCalc)) in validTargetsList[stateHistorySimple[-1][1].split('-')[1]]:
                        # validTargetsList[stateHistorySimple[-1][1].split('-')[1]].append(str(stateExtractionsContext.index(otherServiceStateCalc)))
                # stateHistorySimple.append([currentTemp, str(stateExtractionsCurrentEvent.index(currentEventCalc)) + "-" +str(stateExtractionsContext.index(otherServiceStateCalc)), "",pendingActions[pendingAction]])
                # if not  str(stateExtractionsContext.index(otherServiceStateCalc)) in overallStateExtractions:
                    # overallStateExtractions.append(str(stateExtractionsContext.index(otherServiceStateCalc)))
        # for performedAction in finishedActions:
            # del pendingActions[performedAction]
                    
    state["Time"] = event["Time"]
    stateHistory.append(copy.deepcopy(state))
    found = -1
    #for actionName in event["Actions"]:
        
        #print(state[event["Actions"][actionName]["Service"]]["limitedData"])
        
        
        #exit()
        
        
    for stateCheck in stateOccurances:
        found = 1
        
        for index, elem in enumerate(state):
            if index < (len(state) - 1):
                if stateCheck[1][index] != state[elem]["state"]:
                    found = 0
                    break
        if found == 1:
            stateCheck[0] = stateCheck[0] + 1
            break
    if found == 0 or len(stateOccurances) == 0:
        stateSimple = []
        for index, elem in enumerate(state):
            if index < (len(state) - 1):
                stateSimple.append(state[elem]["state"])
            
        stateOccurances.append([1,stateSimple])

    
    #Implement automatic inference of true states of devices (e.g: on/off)
    affectedServices = {}
    associatedLimitedActions = []
    for trigger in event["Triggers"]:
        if not event["Triggers"][trigger]["Service"] in stateList:
            stateList[event["Triggers"][trigger]["Service"]] = []
            stateOccured[event["Triggers"][trigger]["Service"]] = []
        if not trigger in stateList[event["Triggers"][trigger]["Service"]]:
            stateList[event["Triggers"][trigger]["Service"]].append(trigger)
        stateOccured[event["Triggers"][trigger]["Service"]] = currentStateTime
        #affectedServices.append(event["Triggers"][trigger]["Service"])
        state[event["Triggers"][trigger]["Service"]]["state"] = trigger
        fieldsTotal = ""
        for field in event["Triggers"][trigger]["Fields"]:
            #Hard coded for temperature gathering
            if event["Triggers"][trigger]["Service"] == "AirThings" and field == "Threshhold":
                state[event["Triggers"][trigger]["Service"]]["state"] = event["Triggers"][trigger]["Fields"][field]
            fieldsTotal += event["Triggers"][trigger]["Fields"][field] + ":"
            state[event["Triggers"][trigger]["Service"]]["fields"][field] = event["Triggers"][trigger]["Fields"][field]
        ingredientsTotal = ""
        for ingredient in event["Triggers"][trigger]["Ingredients"]:
            state[event["Triggers"][trigger]["Service"]]["ingredients"][ingredient] = event["Triggers"][trigger]["Ingredients"][ingredient]
            ingredientsTotal += event["Triggers"][trigger]["Ingredients"][ingredient] + ":"
        #stateDefined = trigger + "," + fieldsTotal[:-1] + "," + ingredientsTotal[:-1]
        stateDefined = event["Triggers"][trigger]["Service"] + ":" + trigger
        # if not stateDefined in state[event["Triggers"][trigger]["Service"]]["stateExtractions"]:
            # state[event["Triggers"][trigger]["Service"]]["stateExtractions"].append(stateDefined)
        affectedServices[event["Triggers"][trigger]["Service"]] =  state[event["Triggers"][trigger]["Service"]]["simpleState"]
        
        if event["Triggers"][trigger]["Service"] in limitedActions and trigger in limitedActions[event["Triggers"][trigger]["Service"]]:

            associatedLimitedActions.append(state[event["Triggers"][trigger]["Service"]]["simpleState"] + ":" + str(limitedActions[event["Triggers"][trigger]["Service"]][trigger][0]) + ":" + str(limitedActions[event["Triggers"][trigger]["Service"]][trigger][1]))
            
        
        #state[event["Triggers"][trigger]["Service"]]["simpleState"] = str(state[event["Triggers"][trigger]["Service"]]["stateExtractions"].index(stateDefined))
        state[event["Triggers"][trigger]["Service"]]["simpleState"] = stateDefined
        if not stateDefined in state[event["Triggers"][trigger]["Service"]]['stateExtractions']:
            state[event["Triggers"][trigger]["Service"]]['stateExtractions'].append(stateDefined)


    for action in event["Actions"]:
        if not event["Actions"][action]["Service"] in stateList:
            stateList[event["Actions"][action]["Service"]] = []
            stateOccured[event["Actions"][action]["Service"]] = []
        if not action in stateList[event["Actions"][action]["Service"]]:
            stateList[event["Actions"][action]["Service"]].append(action)
        stateOccured[event["Actions"][action]["Service"]] = currentStateTime
        #affectedServices.append(event["Actions"][action]["Service"])
        state[event["Actions"][action]["Service"]]["state"] = action
        fieldsTotal = ""
        for field in event["Actions"][action]["Fields"]:
            state[event["Actions"][action]["Service"]]["fields"][field] = event["Actions"][action]["Fields"][field]
            fieldsTotal += event["Actions"][action]["Fields"][field] + ":"
        ingredientsTotal = ""
        for ingredient in event["Actions"][action]["Ingredients"]:
            state[event["Actions"][action]["Service"]]["ingredients"][ingredient] = event["Actions"][action]["Ingredients"][ingredient]
            ingredientsTotal += event["Actions"][action]["Ingredients"][ingredient] + ":"
        actionName = action
        
        
        # #print(state[event["Actions"][actionName]["Service"]]["stateExtractions"])    
        
        #stateDefined = actionName + "," + fieldsTotal[:-1] + "," + ingredientsTotal[:-1]
        stateDefined = event["Actions"][actionName]["Service"] + ":" + actionName

        # if not stateDefined in state[event["Actions"][actionName]["Service"]]["stateExtractions"]:
            # state[event["Actions"][actionName]["Service"]]["stateExtractions"].append(stateDefined)
        #state[event["Actions"][actionName]["Service"]]["simpleState"] = str(state[event["Actions"][actionName]["Service"]]["stateExtractions"].index(stateDefined))
        state[event["Actions"][actionName]["Service"]]["simpleState"] = stateDefined

        affectedServices[event["Actions"][actionName]["Service"]] = state[event["Actions"][actionName]["Service"]]["simpleState"]
        if not stateDefined in state[event["Actions"][action]["Service"]]['stateExtractions']:
            state[event["Actions"][action]["Service"]]['stateExtractions'].append(stateDefined)
        #print(event["Actions"][actionName]["Service"])
        # if event["Actions"][actionName]["Service"] == "Android SMS":
            # print(event["Actions"][actionName]["Service"])
            
            # print(event["Actions"][actionName]["Service"] in limitedActions)
            # print(actionName in limitedActions[event["Actions"][action]["Service"]])
            # exit()
        if event["Actions"][actionName]["Service"] in limitedActions and actionName in limitedActions[event["Actions"][action]["Service"]]:

            associatedLimitedActions.append(state[event["Actions"][actionName]["Service"]]["simpleState"] + ":" + str(limitedActions[event["Actions"][actionName]["Service"]][actionName][0]) + ":" + str(limitedActions[event["Actions"][actionName]["Service"]][actionName][1]))
        if actionName in state[event["Actions"][actionName]["Service"]]["limitedData"]:
            #print(state[event["Actions"][actionName]["Service"]]["limitedData"])
            for recordedIndex, recordedEvent in enumerate(state[event["Actions"][actionName]["Service"]]["limitedData"][actionName]["eventTracker"]):
                if currentStateTime - recordedEvent > state[event["Actions"][actionName]["Service"]]["limitedData"][actionName]["timeThreshhold"]:
                    state[event["Actions"][actionName]["Service"]]["limitedData"][actionName]["eventTracker"].remove(recordedEvent)
            if len(state[event["Actions"][actionName]["Service"]]["limitedData"][actionName]["eventTracker"]) < state[event["Actions"][actionName]["Service"]]["limitedData"][actionName]["limit"]:
                state[event["Actions"][actionName]["Service"]]["limitedData"][actionName]["eventTracker"].append(currentStateTime)
            elif len(state[event["Actions"][actionName]["Service"]]["limitedData"][actionName]["eventTracker"]) == state[event["Actions"][actionName]["Service"]]["limitedData"][actionName]["limit"]:
                unsafeStateList.append(["Unsafe State From Repeated Events",state,actionName])
                stateUnsafe = 1
                state[event["Actions"][actionName]["Service"]]["limitedData"][actionName]["eventTracker"].append(currentStateTime)
            #stateDefined = actionName + ":" + str(len(state[event["Actions"][actionName]["Service"]]["limitedData"][actionName]["eventTracker"]))
            #if not stateDefined in state[event["Actions"][actionName]["Service"]]["stateExtractions"]:
                #state[event["Actions"][actionName]["Service"]]["stateExtractions"].append(stateDefined)
            
            #state[event["Actions"][actionName]["Service"]]["simpleState"] += "," + str(len(state[event["Actions"][actionName]["Service"]]["limitedData"][actionName]["eventTracker"]))
        
        # if event["Actions"][actionName]["Service"] == "Android SMS":
            
            # #print(actionName in state[event["Actions"][actionName]["Service"]]["limitedData"])
            # #print(state[event["Actions"][actionName]["Service"]]["simpleState"])
            # #print(str(state[event["Actions"][actionName]["Service"]]["stateExtractions"]))
            
    
    for stateStateIndex, stateState in enumerate(state):
        if stateStateIndex != 0:
            causalFile.write(',')
        if stateState != "Time":

            causalFile.write(str(state[stateState]['stateExtractions'].index(state[stateState]["simpleState"])))
        else:
            causalFile.write(str(state[stateState].hour) + ',' + str(state[stateState].minute))
    currentEventCalc = ""
    otherServiceStateCalc = ""
    otherServicesDicCalc = {}
    traceLineCalc = ""
    
    for stateIndex, testState in enumerate(state):
        
        if not testState == "Time":
            if traceLineCalc != "":
                traceLineCalc += ","
            if len(stateList[testState]) == 1 and currentStateTime - stateOccured[testState] > 1:
                #traceLineCalc += "-1"
                traceLineCalc += str(stateList[testState].index(state[testState]["state"]))

            else:
                traceLineCalc += str(stateList[testState].index(state[testState]["state"]))
        if not testState in affectedServices:
            
                
            if testState == "Time":
                continue
            
                #otherServiceStateCalc += str((state[testState])).split(' ')[1].split(':')[0]
            else:
                if otherServiceStateCalc != "":
                    otherServiceStateCalc += ","
                otherServiceStateCalc += str((state[testState]["simpleState"]))
                otherServicesDicCalc[testState] = str((state[testState]["simpleState"])).split(':')[1]
        else:
            if currentEventCalc != "":
                currentEventCalc += ","
            currentEventCalc += str((state[testState]["simpleState"]))
            if otherServiceStateCalc != "":
                otherServiceStateCalc += ","
            otherServiceStateCalc += str((affectedServices[testState]))
            otherServicesDicCalc[testState] = str((affectedServices[testState])).split(':')[1]
    with open("traceOutput.csv", 'a') as trace_output:
        trace_output.write(traceLineCalc + "\n")
    if not currentEventCalc in stateExtractionsCurrentEvent:
        stateExtractionsCurrentEvent.append(currentEventCalc)
    if not otherServiceStateCalc in stateExtractionsContext:
        stateExtractionsContext.append(otherServiceStateCalc)
        stateExtractionsContextDict.append(otherServicesDicCalc)
    if int(sys.argv[4]) == 0:
        stateHistorySimple.append([currentStateTime, str(stateExtractionsCurrentEvent.index(currentEventCalc)) + ":" + str(stateExtractionsContext.index(otherServiceStateCalc)), event["Time"]])
        if len(associatedLimitedActions) > 0:
            for elem in  associatedLimitedActions:
                if elem in limitedActionList:
                    if not str(stateExtractionsCurrentEvent.index(currentEventCalc)) in limitedActionList[elem]:
                        
                        limitedActionList[elem].append(str(stateExtractionsCurrentEvent.index(currentEventCalc)))
                else:
                    limitedActionList[elem] = [str(stateExtractionsCurrentEvent.index(currentEventCalc))]
        if not str(stateExtractionsCurrentEvent.index(currentEventCalc)) + ":" + str(stateExtractionsContext.index(otherServiceStateCalc)) in overallStateExtractions:
            overallStateExtractions.append(str(stateExtractionsCurrentEvent.index(currentEventCalc)) + ":" + str(stateExtractionsContext.index(otherServiceStateCalc)))
        #stateHistorySimple.append([currentStateTime, overallStateExtractions.index(str(stateExtractionsCurrentEvent.index(currentEventCalc)) + ":" + str(stateExtractionsContext.index(otherServiceStateCalc)))])

    elif int(sys.argv[4]) == 1:
        #stateHistorySimple.append([currentStateTime, str(stateExtractionsContext.index(otherServiceStateCalc)), event["Time"]])
        associatedStates = ""
        if len(associatedLimitedActions) > 0 and len(stateHistorySimple) > 0:
            for elem in associatedLimitedActions:

                oldContext = stateHistorySimple[-1][1]
                if oldContext in limitedActionList:
                    # associatedStates += str(limitedActionList.index(elem)) + "_"
                    if not str(stateExtractionsCurrentEvent.index(currentEventCalc)) in limitedActionList[oldContext]:
                        limitedActionList[oldContext][str(stateExtractionsCurrentEvent.index(currentEventCalc))] = str(stateExtractionsContext.index(otherServiceStateCalc))
                else:
                    # associatedStates += str(len(limitedActionList)) + "_"
                    # limitedActionList.append(elem)
                    limitedActionList[oldContext] = {}
                    limitedActionList[oldContext][str(stateExtractionsContext.index(otherServiceStateCalc))] = str(stateExtractionsCurrentEvent.index(currentEventCalc))
        if len(stateHistorySimple) > 0:
            if not stateHistorySimple[-1][1].split('-')[1] in transitionList:
                transitionList[stateHistorySimple[-1][1].split('-')[1]] = {}
                validTargetsList[stateHistorySimple[-1][1].split('-')[1]] = []
            transitionList[stateHistorySimple[-1][1].split('-')[1]][str(stateExtractionsCurrentEvent.index(currentEventCalc))] = str(stateExtractionsContext.index(otherServiceStateCalc))
            transitionList[stateHistorySimple[-1][1].split('-')[1]][str(stateExtractionsContext.index(otherServiceStateCalc)) + '-c'] = str(stateExtractionsCurrentEvent.index(currentEventCalc))
            if not str(stateExtractionsContext.index(otherServiceStateCalc)) in validTargetsList[stateHistorySimple[-1][1].split('-')[1]]:
                validTargetsList[stateHistorySimple[-1][1].split('-')[1]].append(str(stateExtractionsContext.index(otherServiceStateCalc)))
        if associatedStates == "":
            stateHistorySimple.append([currentStateTime, str(stateExtractionsCurrentEvent.index(currentEventCalc)) + "-" +str(stateExtractionsContext.index(otherServiceStateCalc)), "",event["Time"]])
            #stateHistorySimple.append([currentStateTime, str(stateExtractionsContext.index(otherServiceStateCalc)), "",event["Time"]])
        else:
            stateHistorySimple.append([currentStateTime, str(stateExtractionsCurrentEvent.index(currentEventCalc)) + "-" +str(stateExtractionsContext.index(otherServiceStateCalc)), associatedStates[:-1],event["Time"]])
            #stateHistorySimple.append([currentStateTime, str(stateExtractionsContext.index(otherServiceStateCalc)), associatedStates[:-1],event["Time"]])
        #if not str(stateExtractionsContext.index(otherServiceStateCalc)) in overallStateExtractions:
        if not  str(stateExtractionsContext.index(otherServiceStateCalc)) in overallStateExtractions:
            overallStateExtractions.append(str(stateExtractionsContext.index(otherServiceStateCalc)))
            #overallStateExtractions.append( str(stateExtractionsCurrentEvent.index(currentEventCalc)) + "-" + str(stateExtractionsContext.index(otherServiceStateCalc)))
    else:    
        stateHistorySimple.append([currentStateTime, str(stateExtractionsCurrentEvent.index(currentEventCalc)),event["Time"]])
        if not str(stateExtractionsCurrentEvent.index(currentEventCalc)) in overallStateExtractions:
            overallStateExtractions.append(str(stateExtractionsCurrentEvent.index(currentEventCalc)))
        #stateHistorySimple.append([currentStateTime, overallStateExtractions.index(str(stateExtractionsCurrentEvent.index(currentEventCalc)))])
        

    #print(str(stateExtractionsCurrentEvent.index(currentEventCalc)) + "," + str(stateExtractionsContext.index(otherServiceStateCalc)))
    # if not stateHistoryCalc in stateHistorySimpleRecord:
        # stateHistorySimpleRecord.append(stateHistoryCalc)
    if currentStateTimeVar != None:
        timeDif = str(state["Time"] - currentStateTimeVar)
        if "day" in timeDif:
            daysPassed = abs(int(timeDif.split('day')[0]))
            timeDif = timeDif.split(',')[1][1:]
        else:
            daysPassed = 0
        timeDif = timeDif.split(':')
        hoursPassed = int(timeDif[0])
        minutesPassed = int(timeDif[1])
        currentStateTime += (daysPassed*1440) + (hoursPassed*60) + minutesPassed
    currentStateTimeVar = state["Time"]
    # stateHistorySimple.append([currentStateTime,stateHistorySimpleRecord.index(stateHistoryCalc)])
    # if stateUnsafe == 1 and not stateHistorySimpleRecord.index(stateHistoryCalc) in simpleUnsafeStates:
        # simpleUnsafeStates.append(stateHistorySimpleRecord.index(stateHistoryCalc))
def getNecessaryDurations(policyElement,fullPolicy):
    durationsTracking = []
    results = []
    
    for index, part in enumerate(policyElement[0]):
        if type(part) is list:
            if part[0] == "Time":
                continue
            if not part[0] in state or part[-1] == None:
                continue
            
            
            if len(part) == 4:
                if state[part[0]]['state'] != part[1]:
                    durationsTracking.append(part)
            else:    
                if state[part[0]]['state'] == part[1]:
                    durationsTracking.append(part)
        else:
            for durElem in getNecessaryDurations(fullPolicy[part],fullPolicy):
                durationsTracking.append(durElem)
    return durationsTracking
   
            
def checkStateViolation(policyElement,fullPolicy,time,useTime):
    global state, unsafeDurationTracker
    unsafeTimeTracker = []
    calculatedTimes = []
    flipTracker = []
    results = []
    causeDescription = []

    for index, part in enumerate(policyElement[0]):

        if type(part) is list:
            if not part[0] in state:
                return [False]
            
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
                #flipTracker.append(len(unsafeTimeTracker)-1)
                flipTracker.append(0)
            elif len(part) == 4:
                results.append(state[part[0]]['state'] != part[1])
                causeDescription.append(part[0] + ":" +part[1] + "NOT")
            else:    
                
                results.append(state[part[0]]['state'] == part[1])  
                causeDescription.append(part[0] + ":" +part[1] + "WAS")
            flipTracker.append(0)
        else:
            callResult = checkStateViolation(fullPolicy[part],fullPolicy,time,useTime)
            results.append(callResult[0])
            # if len(callResult[1]) > 0:
                # unsafeTimeTracker.append(callResult[1])
                # flipTracker.append(len(unsafeTimeTracker)-1)
            
            
        
        # returnCalc = -1
        # couldFlip = "NO"
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
            # return [returnCalc,unsafeTimeTracker]
    
        
whichOccured = {}    
safeStates = 0
def checkIfStateIsUnsafe(event, nextEvent):
    global state, unsafeStateListLiteral, stateHistorySimple
    global whichOccured, safeStates, pendingActions
    safestate = 1
    #print(unsafeStates)
    for unsafeIndex, unsafeState in enumerate(unsafeStates):
        #if unsafeIndex != 0 and unsafeIndex != 1:
        #    continue
        checkViolationsResult = checkStateViolation(unsafeStates[unsafeState]['0'],unsafeStates[unsafeState],None,0)
        # if state["AirThings"]["state"] == "Temperature rises above threshold" and unsafeIndex == 3:
            # print(state["AirThings"]["state"])
            # print(state["Wemo SmartPlug"]["state"])
            
            
            # exit()
        # if unsafeState == 0:
            #print(unsafeStates[unsafeState])
            # if len(state["soil_sensor1_temp"]["stateExtractions"]) == 4:
                # print(state["soil_sensor1_temp"]["stateExtractions"])
                # print(state["soil_sensor1_temp"]["state"])
                # print(checkViolationsResult)
                # exit()
            # #exit()
        if checkViolationsResult[0]:
            
            violatingTimes = []
            if unsafeIndex == 0 or unsafeIndex == 1:
                if not  "Magic Hue:Turn off lights" in pendingActions:
                    pendingActions["Magic Hue:Turn off lights"] = event["Time"] + datetime.timedelta(minutes = random.randint(3,10))
            if unsafeIndex == 2 or unsafeIndex == 3:
                if not  "Wemo SmartPlug:Turn off" in pendingActions:
                    pendingActions["Wemo SmartPlug:Turn off"] = event["Time"] + datetime.timedelta(minutes = random.randint(3,10))
            if unsafeIndex == 5 or unsafeIndex == 6:
                if not  "Wemo SmartPlug:Turn on" in pendingActions:
                    pendingActions["Wemo SmartPlug:Turn on"] = event["Time"] + datetime.timedelta(minutes = random.randint(3,10))
            if len(unsafeStates[unsafeState]['0'][1]) > 0:
                for timeCheckIndex, timeCheck in enumerate(unsafeStates[unsafeState]['0'][1]):
                    if len(timeCheck) == 1 and checkStateViolation(unsafeStates[unsafeState]['0'],unsafeStates[unsafeState],(timeCheck[0]).time(),1)[0]:
                        startBound = str(timeCheck[0].hour) + ':' + str(timeCheck[0].minute)
                        endBound = str(timeCheck[0].hour) + ':' + str(timeCheck[0].minute)
                        violatingTimes.append(startBound + '/' + endBound)
                    else:
                        
                        inside = str(timeCheck[0].hour) + ':' + str(timeCheck[0].minute) + '/' + str(timeCheck[1].hour) + ':' + str(timeCheck[1].minute)
                        outside = str((timeCheck[1]+datetime.timedelta(minutes=1)).time().hour) + ':' + str((timeCheck[1]+datetime.timedelta(minutes=1)).time().minute) + '/' + str((timeCheck[0]-datetime.timedelta(minutes=1)).time().hour) + ':' + str((timeCheck[0]-datetime.timedelta(minutes=1)).time().minute)
                        if checkStateViolation(unsafeStates[unsafeState]['0'],unsafeStates[unsafeState],(timeCheck[0]).time(),1)[0]:
                            violatingTimes.append(inside)
                        elif checkStateViolation(unsafeStates[unsafeState]['0'],unsafeStates[unsafeState],(timeCheck[1]+datetime.timedelta(minutes=1)).time(),1)[0]:
                            violatingTimes.append(outside)
                                                    

                   
                if len(violatingTimes) == 0:
                    continue
            unsafeStateList.append(["Unsafe State From Event",state,unsafeState])
            safestate = 0
            if not stateHistorySimple[-1][1] + '-' + str(unsafeIndex) in simpleUnsafeStates:
                    
                if unsafeStates[unsafeState]["Duration"]:
                    durationHappened = getNecessaryDurations(unsafeStates[unsafeState]['0'],unsafeStates[unsafeState]).copy()
                    if not stateHistorySimple[-1][1]  in simpleDurationsTracker:
                        simpleDurationsTracker[stateHistorySimple[-1][1]] = [durationHappened,[]]
                    simpleDurationsTracker[stateHistorySimple[-1][1]][1].append([str(unsafeIndex)])
                if not unsafeIndex in whichOccured:
                    whichOccured[unsafeIndex] = 0
                whichOccured[unsafeIndex] += 1
                simpleUnsafeStates[stateHistorySimple[-1][1] + '-' + str(unsafeIndex)] = [violatingTimes,checkViolationsResult[1]]

    if safestate == 1:
        safeStates += 1
    for secureIndex, secureInfo in enumerate(secureInformation):
        triggerName = list(event["Triggers"])[0]
        if event["Triggers"][triggerName]["Service"] == secureInfo[0] and (secureInfo[1] == "" or secureInfo[1] == triggerName):
            match = 1
            for field in secureInfo[2]:
                fieldSplit = field.split(":")
                if "-" in fieldSplit[1]:
                    valueSplit = fieldSplit[1].split("-")
                    if event["Triggers"][triggerName]["Fields"][fieldSplit[0]] < float(valueSplit[0]) or event["Triggers"][triggerName]["Fields"][fieldSplit[0]] > float(valueSplit[1]):
                        match = 0
                        break
                elif "+" in fieldSplit[1]:
                    valueSplit = fieldSplit[1].split("+")
                    found = 0
                    for value in valueSplit:
                        if event["Triggers"][triggerName]["Fields"][fieldSplit[0]] == value:
                            found = 1
                    if found == 0:
                        match = 0
                        break
                elif event["Triggers"][triggerName]["Fields"][fieldSplit[0]] != fieldSplit[1]:
                    match = 0
                    break
            if match == 0:
                continue
            for ingredient in secureInfo[3]:
                ingredientSplit = ingredient.split(":")
                if "-" in ingredientSplit[1]:
                    valueSplit = ingredientSplit[1].split("-")
                    if event["Triggers"][triggerName]["Ingredients"][ingredientSplit[0]] < float(valueSplit[0]) or event["Triggers"][triggerName]["Ingredients"][ingredientSplit[0]] > float(valueSplit[1]):
                        match = 0
                        break
                elif "+" in ingredientSplit[1]:
                    valueSplit = ingredientSplit[1].split("+")
                    found = 0
                    for value in valueSplit:
                        if event["Triggers"][triggerName]["Ingredients"][ingredientSplit[0]] == value:
                            found = 1
                    if found == 0:
                        match = 0
                        break
                elif event["Triggers"][triggerName]["Ingredients"][ingredientSplit[0]] != ingredientSplit[1]:
                    match = 0
                    break
            if match == 0:
                continue
            if secureInfo[4] == "Whitelist":
                for query in event["Queries"]:
                    whitelisted = 0
                    for service in secureInfo[4]:
                        if query == service:
                            whitelisted = 1
                    if whitelisted == 0:
                        if secureInfo[5] == 1:
                            for field in event["Queries"][query]["Fields"]:
                                for ingredient in secureInfo[3]:
                                    ingredientSplit = ingredient.split(":")
                                    if ingredientSplit[0] in event["Queries"][query]["Fields"][field]:
                                        unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,query])
                                        if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                            #print("Here3")
                                            simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                            #Check filter code for leaks, currently only if both the private information and a non-allowed sink are both present, not checking for direct leaks, and check if action fields are modified
                            #Need to modify so that it checks if any actions are modified or skipped
                            #Remove query, cannot leak information
                            if triggerName in event["Filter"] and query in event["Filter"]:
                                unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,query])
                                if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                    simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                        else:
                            unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,query])
                            if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                    simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                for action in event["Actions"]:
                    whitelisted = 0
                    for service in secureInfo[4]:
                        if action == service:
                            whitelisted = 1
                    if whitelisted == 0:
                        if secureInfo[5] == 1:
                            for field in event["Actions"][action]["Fields"]:
                                for ingredient in secureInfo[3]:
                                    ingredientSplit = ingredient.split(":")
                                    if ingredientSplit[0] in event["Actions"][action]["Fields"][field]:
                                        unsafeStateList.append(["Unsafe State From Information Leak",event,secureInfo,action])
                                        if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                            simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                            #Check filter code for leaks, currently only if both the private information and a non-allowed sink are both present, not checking for direct leaks
                            if triggerName in event["Filter"] and action in event["Filter"]:
                                unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,action])
                                if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                    simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                        else:
                            unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,action])
                            if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:

                                    simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
            if secureInfo[4] == "Blacklist":
                for service in secureInfo[4]:
                    for query in event["Queries"]:
                        if service == query:
                            if secureInfo[5] == 1:
                                for field in event["Queries"][query]["Fields"]:
                                    for ingredient in secureInfo[3]:
                                        ingredientSplit = ingredient.split(":")
                                        if ingredientSplit[0] in event["Queries"][query]["Fields"][field]:
                                            unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,query])
                                            if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                                #print("Here9")
                                                simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                                #Check filter code for leaks, currently only if both the private information and a non-allowed sink are both present, not checking for direct leaks
                                if triggerName in event["Filter"] and query in event["Filter"]:
                                    unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,query])
                                    if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                        #print("Here10")
                                        simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                            else:
                                unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,query])
                                if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                    #print("Here11")
                                    simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                    for action in event["Actions"]:
                        if service == query:
                            if secureInfo[5] == 1:
                                for field in event["Actions"][action]["Fields"]:
                                    for ingredient in secureInfo[3]:
                                        ingredientSplit = ingredient.split(":")
                                        if ingredientSplit[0] in event["Actions"][action]["Fields"][field]:
                                            unsafeStateList.append(["Unsafe State From Information Leak",event,secureInfo,action])
                                            if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                                #print("Here12")
                                                simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                                #Check filter code for leaks, currently only if both the private information and a non-allowed sink are both present, not checking for direct leaks
                                if triggerName in event["Filter"] and action in event["Filter"]:
                                    unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,action])
                                    if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                        #print("Here14")
                                        simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                            else:
                                unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,action])
                                if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                    #print("Here15")
                                    simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
        for query in event["Queries"]:
            if event["Queries"][query]["Service"] == secureInfo[0] and (secureInfo[1] == "" or secureInfo[1] == query):
                match = 1
                for field in secureInfo[2]:
                    fieldSplit = field.split(":")
                    if "-" in fieldSplit[1]:
                        valueSplit = fieldSplit[1].split("-")
                        if event["Queries"][query]["Fields"][fieldSplit[0]] < float(valueSplit[0]) or event["Queries"][query]["Fields"][fieldSplit[0]] > float(valueSplit[1]):
                            match = 0
                            break
                    elif "+" in fieldSplit[1]:
                        valueSplit = fieldSplit[1].split("+")
                        found = 0
                        for value in valueSplit:
                            if event["Queries"][query]["Fields"][fieldSplit[0]] == value:
                                found = 1
                        if found == 0:
                            match = 0
                            break
                    elif event["Queries"][query]["Fields"][fieldSplit[0]] != fieldSplit[1]:
                        match = 0
                        break
                if match == 0:
                    continue
                for ingredient in secureInfo[3]:
                    ingredientSplit = ingredient.split(":")
                    if "-" in ingredientSplit[1]:
                        valueSplit = ingredientSplit[1].split("-")
                        if event["Queries"][query]["Ingredients"][ingredientSplit[0]] < float(valueSplit[0]) or event["Queries"][query]["Ingredients"][ingredientSplit[0]] > float(valueSplit[1]):
                            match = 0
                            break
                    elif "+" in ingredientSplit[1]:
                        valueSplit = ingredientSplit[1].split("+")
                        found = 0
                        for value in valueSplit:
                            if event["Queries"][query]["Ingredients"][ingredientSplit[0]] == value:
                                found = 1
                        if found == 0:
                            match = 0
                            break
                    elif event["Queries"][query]["Ingredients"][ingredientSplit[0]] != ingredientSplit[1]:
                        match = 0
                        break
                if match == 0:
                    continue
                if secureInfo[4] == "Whitelist":
                    for query in event["Queries"]:
                        whitelisted = 0
                        for service in secureInfo[4]:
                            if query == service:
                                whitelisted = 1
                        if whitelisted == 0:
                            if secureInfo[5] == 1:
                                for field in event["Queries"][query]["Fields"]:
                                    for ingredient in secureInfo[3]:
                                        ingredientSplit = ingredient.split(":")
                                        if ingredientSplit[0] in event["Queries"][query]["Fields"][field]:
                                            unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,query])
                                            if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                                #print("Here16")
                                                simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                                #Check filter code for leaks, currently only if both the private information and a non-allowed sink are both present, not checking for direct leaks
                                if triggerName in event["Filter"] and query in event["Filter"]:
                                    unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,query])
                                    if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                        #print("Here17")
                                        simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                            else:
                                unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,query])
                                if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                    #print("Here18")
                                    simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                    for action in event["Actions"]:
                        whitelisted = 0
                        for service in secureInfo[4]:
                            if action == service:
                                whitelisted = 1
                        if whitelisted == 0:
                            if secureInfo[5] == 1:
                                for field in event["Actions"][action]["Fields"]:
                                    for ingredient in secureInfo[3]:
                                        ingredientSplit = ingredient.split(":")
                                        if ingredientSplit[0] in event["Actions"][action]["Fields"][field]:
                                            unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,action])
                                            if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                                #print("Here19")
                                                simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                                #Check filter code for leaks, currently only if both the private information and a non-allowed sink are both present, not checking for direct leaks
                                if triggerName in event["Filter"] and action in event["Filter"]:
                                    unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,action])
                                    if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                        #print("Here20")
                                        simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                            else:
                                unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,action])
                                if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                    #print("Here21")
                                    simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                if secureInfo[4] == "Blacklist":
                    for service in secureInfo[4]:
                        for query in event["Queries"]:
                            if service == query:
                                if secureInfo[5] == 1:
                                    for field in event["Queries"][query]["Fields"]:
                                        for ingredient in secureInfo[3]:
                                            ingredientSplit = ingredient.split(":")
                                            if ingredientSplit[0] in event["Queries"][query]["Fields"][field]:
                                                unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,query])
                                                if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                                    #print("Here22")
                                                    simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                                    #Check filter code for leaks, currently only if both the private information and a non-allowed sink are both present, not checking for direct leaks
                                    if triggerName in event["Filter"] and query in event["Filter"]:
                                        unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,query])
                                        if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                            #print("Here23")
                                            simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                                else:
                                    unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,query])
                                    if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                        #print("Here24")
                                        simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                        for action in event["Actions"]:
                            if service == query:
                                if secureInfo[5] == 1:
                                    for field in event["Actions"][action]["Fields"]:
                                        for ingredient in secureInfo[3]:
                                            ingredientSplit = ingredient.split(":")
                                            if ingredientSplit[0] in event["Actions"][action]["Fields"][field]:
                                                unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,action])
                                                if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                                    #print("Here25")
                                                    simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                                    #Check filter code for leaks, currently only if both the private information and a non-allowed sink are both present, not checking for direct leaks
                                    if triggerName in event["Filter"] and action in event["Filter"]:
                                        unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,action])
                                        if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                            #print("Here26")
                                            simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                                else:
                                    unsafeStateList.append(["Unsafe State From Information Leak",state,secureInfo,action])
                                    if not [stateHistorySimple[-1][1],unsafeState[-1]] in simpleUnsafeStates:
                                        #print("Here27")
                                        simpleUnsafeStates[stateHistorySimple[-1][1] + "-" + str(secureIndex + len(unsafeStates))] = []
                    
    #print("No unsafe states")
                
                                           
#Open up a refined file with the formatted provenance data
#file1 = open('ProvDataRefinedNew.txt', 'r', errors='ignore', encoding='utf-8')
#file1 = open('individualProvFixed.txt', 'r', errors='ignore', encoding='utf-8')
#file1 = open('newProvenance.txt', 'r', errors='ignore', encoding='utf-8')
file1 = open('agricultureData.txt', 'r', errors='ignore', encoding='utf-8')
#file1 = open('convertedFile.txt', 'r', errors='ignore', encoding='utf-8')


initializing = 0
lineNum = 0

#Read the entire file line by line and gather information on all services, including all possible elements and their meta-information
while True:
    line = file1.readline()
    # if "\n" in line[-3:]:
        # line = line[:-3]
    line = line.replace("\n","")
    line = line.replace("\\n","")
    line = line.replace('\\xa0',' ')
    #line = line.replace('\\n',' ')
    
    #printable = set(string.printable)
    #filter(lambda x: x in #printable, line)
    line = re.sub(r"\\x([0-9]|[a-z])([0-9]|[a-z])","",line)
    lineNum += 1
    #line = line.replace("\n","")
    #line = line.replace("\n","")
    # if lineNum >= 5000:
        # break

    if not line:
        break
    if line == "InitialState":
        initializing = 1
        continue
    elif line == "InitialStateEnd":
        initializing = 0
        continue
    if initializing == 1:
        stateSplit = line.split("/")
        initialStateData.append(stateSplit)
        continue
    distinctElements = []
    if "-" in line:
        distinctElements = line.split("-")
    else:
        distinctElements = [line]
    currentService = ""
    currentName = ""
    currentField = ""
    currentIngredient = ""  
    elementType = -1
    fieldPart = ""
    fieldPotentialValue = ""
    ingredientPart = ""
    ingredientPotentialValue = ""
    eventBreakdown = {"Triggers":{},"Queries":{},"Actions":{}}
    elements = ["Triggers","Queries","Actions"]
    fieldPart = ""
    fieldName = ""
    ingredientPart = ""
    ingredientName = ""

    for element in distinctElements:
        
        if "," in line:
            parsedElement = element.split(",")
        else:
            parsedElement = [element]
        for chunk in parsedElement:
            if "\ufeff" in chunk:
                chunk = chunk.replace("\ufeff","")
            if ":" in chunk:
                chunkSplit = chunk.split(":")
                #Perform state extraction from current chunk
                if currentService != "":
                    for stateExtraction in stateExtractionHeuristics:
                            if stateExtraction[0].lower() in chunkSplit[1].lower() and not stateExtraction[1] in services[currentService].stateExtractions:
                                services[currentService].stateExtractions.append(stateExtraction[1])
                if chunkSplit[0] == "TriggerID":
                    elementType = 0
                    currentService = chunkSplit[1]
                    ingredientPotentialValue = ""
                    fieldPotentialValue = ""
                    if not chunkSplit[1] in services:
                        newService = Service("initial")
                        services[currentService] = newService
                
                        
                elif chunkSplit[0] == "QueryID":
                    elementType = 1
                    currentService = chunkSplit[1]
                    ingredientPotentialValue = ""
                    fieldPotentialValue = ""
                    if not chunkSplit[1] in services:
                        newService = Service("initial")
                        services[currentService] = newService
                        
                elif chunkSplit[0] == "ActionID" and chunkSplit[1] != "Action Skipped":
                    elementType = 2
                    currentService = chunkSplit[1]
                    ingredientPotentialValue = ""
                    fieldPotentialValue = ""

                    if not chunkSplit[1] in services:
                        newService = Service("initial")
                        services[currentService] = newService  
                        
                elif chunkSplit[0] == "TriggerName":
                    elementType = 0
                    currentName = chunkSplit[1]
                    ingredientPotentialValue = ""
                    fieldPotentialValue = ""
                    eventBreakdown["Triggers"][currentName] = {"Service":currentService,"Fields":{},"Ingredients":{}}
                    if not chunkSplit[1] in services[currentService].elements[elementType]:
                        newTrigger = Trigger()
                        services[currentService].elements[elementType][currentName] = newTrigger
                    else:
                        services[currentService].elements[elementType][currentName] .occurances += 1
                    
                    
                        
                elif chunkSplit[0] == "QueryName":
                    elementType = 1
                    currentName = chunkSplit[1]
                    ingredientPotentialValue = ""
                    fieldPotentialValue = ""
                    eventBreakdown["Queries"][currentName] = {"Service":currentService,"Fields":{},"Ingredients":{}}
                    if not chunkSplit[1] in services[currentService].elements[elementType]:
                        newQuery = Query()
                        services[currentService].elements[elementType][currentName] = newQuery
                    else:
                        services[currentService].elements[elementType][currentName] .occurances += 1
                        
                    
                        
                elif chunkSplit[0] == "ActionName":
                    elementType = 2
                    currentName = chunkSplit[1]
                    ingredientPotentialValue = ""
                    fieldPotentialValue = ""
                    eventBreakdown["Actions"][currentName] = {"Service":currentService,"Fields":{},"Ingredients":{}}
                    if not chunkSplit[1] in services[currentService].elements[elementType]:
                        newAction = Action()
                        services[currentService].elements[elementType][currentName] = newAction
                    else:
                        services[currentService].elements[elementType][currentName] .occurances += 1

                elif chunkSplit[0] == "TriggerFields" or chunkSplit[0] == "QueryFields" or chunkSplit[0] == "ActionFields" or fieldPart != "":
                    ingredientPotentialValue = ""
                    filterPotentialValue = ""
                    if ";" in chunkSplit[1]:
                        fieldSplit = chunkSplit[1].split(";")
                    else:
                        fieldSplit = [chunkSplit[1]]
                    fieldPart = ""
                    fieldName = ""
                    fieldIndividualSplit = []
                    for field in fieldSplit:
                        if (not "/" in field) and fieldName == "":
                            fieldPart = fieldPart + field
                        elif "/" in field:
                            fieldIndividualSplit = field.split("/")
                            fieldName = fieldPart + fieldIndividualSplit[0]
                            fieldValue = fieldIndividualSplit[1]
                            fieldPotentialValue = fieldValue
                            fieldPart = ""
                            if fieldName in services[currentService].elements[elementType][currentName].fields and not fieldValue in services[currentService].elements[elementType][currentName].fields[fieldName]:
                                services[currentService].elements[elementType][currentName].fields[fieldName].append(fieldValue)
                                eventBreakdown[elements[elementType]][currentName]["Fields"][fieldName] = fieldValue
                            else:
                                services[currentService].elements[elementType][currentName].fields[fieldName] = [fieldValue]
                                eventBreakdown[elements[elementType]][currentName]["Fields"][fieldName] = fieldValue
                        else:
                            
                            print("Should not get here 1")
                            exit()
                            
                elif chunkSplit[0] == "TriggerIngredients" or chunkSplit[0] == "QueryIngredients" or ingredientPart != "":
                    fieldPotentialValue = ""
                    filterPotentialValue = ""
                    if ";" in chunkSplit[1]:
                        ingredientSplit = chunkSplit[1].split(";")
                    else:
                        ingredientSplit = [chunkSplit[1]]

                    ingredientIndividualSplit = []
                    for ingredient in ingredientSplit:
                        
                        
                        if (not "/" in ingredient): #and ingredientName == "":
                            ingredientPart = ingredientPart + ingredient
                        elif "/" in ingredient:
                            ingredientIndividualSplit = ingredient.split("/")
                            ingredientName = ingredientPart + ingredientIndividualSplit[0]
                            ingredientValue = ingredientIndividualSplit[1]
                            ingredientPotentialValue = ingredientValue
                            ingredientPart = ""
                            if ingredientName in services[currentService].elements[elementType][currentName].ingredients and not ingredientValue in services[currentService].elements[elementType][currentName].ingredients[ingredientName]:
                                services[currentService].elements[elementType][currentName].ingredients[ingredientName].append(ingredientValue)
                                eventBreakdown[elements[elementType]][currentName]["Ingredients"][ingredientName] = ingredientValue
                            else:
                                services[currentService].elements[elementType][currentName].ingredients[ingredientName] = [ingredientValue]
                                eventBreakdown[elements[elementType]][currentName]["Ingredients"][ingredientName] = ingredientValue
                        else:
                            
                            
                            
                            print("Should not get here 2")
                            exit()
                            
                elif chunkSplit[0] == "filter":
                    fieldPotentialValue = ""
                    ingredientPotentialValue = ""
                    filterPotentialValue = chunkSplit[1]
                    eventBreakdown["Filter"] = chunkSplit[1]
                    if not chunkSplit[1] in services[currentService].elements[3]:
                        services[currentService].elements[3].append(chunkSplit[1])
                        
                else:
                    if fieldPotentialValue != "":
                        services[currentService].elements[elementType][currentName].fields[fieldName][-1] = services[currentService].elements[elementType][currentName].fields[fieldName][-1] + "," + chunk
                        eventBreakdown[elements[elementType]][currentName]["Fields"][fieldName] = eventBreakdown[elements[elementType]][currentName]["Fields"][fieldName] + "," + chunk
                        fieldPart = ""
                        
                    elif ingredientPotentialValue != "":
                        services[currentService].elements[elementType][currentName].ingredients[ingredientName][-1] = services[currentService].elements[elementType][currentName].ingredients[ingredientName][-1] + "," + chunk
                        eventBreakdown[elements[elementType]][currentName]["Ingredients"][ingredientName] = eventBreakdown[elements[elementType]][currentName]["Ingredients"][ingredientName] + "," + chunk
                        ingredientPart = ""
                    elif fieldPotentialValue != "":
                        newFilter = eventBreakdown["Filter"] + "," + chunk
                        if not newFilter in services[currentService].elements[3]:
                            services[currentService].elements[3][-1] = newFilter
                        else:
                            del services[currentService].elements[3][-1]
                        eventBreakdown["Filter"] = newFilter
    
    #Here we get the date and time, think of a better way to do it (at least fix that URL cuts of month causing the below code fixes)
    
    

    if len(re.findall("\\\\x([0-9]|[a-z])([0-9]|[a-z])",line)) > 0:
      print("Unreadable character not removed")
      exit()
    #if len(re.findall('[a-zA-Z]* [0-9]*, [0-9]* at [0-9][0-9]:[0-9][0-9]',line)) > 0:

    currentSelected = -1
    

    #if lineNum == 824:
            #print(re.findall('[a-zA-Z]* [0-9]*, [0-9]* at [0-9]*:[0-9][0-9][a-zA-Z][a-zA-Z]',line))
    # if lineNum < 600:
        # print(lineNum)

    for datePossible in re.findall('[a-zA-Z]* [0-9]*, [0-9]* at [0-9]*:[0-9][0-9][a-zA-Z][a-zA-Z]',line):
        dateSplit = datePossible.split(" ")

        eventDayTemp = int(dateSplit[1][:-1])
        eventYearTemp = int(dateSplit[2])
        eventTimeSplitTemp = dateSplit[4].split(":")       
        eventHourTemp = int(eventTimeSplitTemp[0])%12
        if eventTimeSplitTemp[1][2:] == "PM":
            eventHourTemp += 12
        eventMinuteTemp = int(eventTimeSplitTemp[1][:-2])
        if dateSplit[0][:3].lower() in months:
            eventMonthTemp = months.index(dateSplit[0][:3].lower())
        else:
            eventMonthTemp = eventMonth

        if eventDayTemp == 31 and eventMonthTemp == 9:
            eventDayTemp = 30
        eventTimeTemp = datetime.datetime(eventYearTemp,eventMonthTemp,eventDayTemp,eventHourTemp,eventMinuteTemp)

        if eventTime != None:
            if not eventTimeTemp < eventTime and (currentSelected == -1 or eventTimeTemp > currentSelected):
                currentSelected = eventTimeTemp
        elif currentSelected == -1 or ((eventTimeTemp - eventTime) > (currentSelected - eventTime)):
            currentSelected = eventTimeTemp
    if currentSelected != -1:
        # dateInfo = re.findall('[a-zA-Z]* [0-9]*, [0-9]* at [0-9][0-9]:[0-9][0-9][a-zA-Z][a-zA-Z]',line)[0]
        # dateSplit = dateInfo.split(" ")
        # if dateSplit[0][:3].lower() in months:
            # eventMonth = months.index(dateSplit[0][:3].lower())
        # #else:
        # #    eventMonth = 3
        # eventDay = int(dateSplit[1][:-1])
        # eventYear = int(dateSplit[2])
        # eventTimeSplit = dateSplit[4].split(":")
        # eventHour = int(eventTimeSplit[0])%12
        # if eventTimeSplit[1][2:] == "PM":
            # eventHour += 12
        # eventMinute = int(eventTimeSplit[1][:-2])
        # if dateSplit[0][:3].lower() in months:
            # eventMonthTemp = months.index(dateSplit[0][:3].lower())
        # else:
            # eventMonthTemp = eventMonth

        
        if eventTime != None:
            # if eventDay == 31 and eventMonth == 9:
                # eventDay = 30
            #timeDif = str(datetime.datetime(eventYear,eventMonth,eventDay,eventHour,eventMinute) - eventTime)
            timeDif = str(currentSelected - eventTime)
            if "day" in timeDif:
                daysPassed = abs(int(timeDif.split('day')[0]))
                timeDif = timeDif.split(',')[1][1:]
            else:
                daysPassed = 0
            timeDif = timeDif.split(':')
            hoursPassed = int(timeDif[0])
            minutesPassed = int(timeDif[1])
            currentTime += (daysPassed*1440) + (hoursPassed*60) + minutesPassed
            #currentTime += datetime.datetime(eventYear,eventMonth,eventDay,eventHour,eventMinute) - eventTime
        else:
            currentTime = 0
        #eventTime = datetime.datetime(eventYear,eventMonth,eventDay,eventHour,eventMinute)
        eventTime = currentSelected
        #eventBreakdown["Time"] = datetime.datetime(eventYear,eventMonth,eventDay,eventHour,eventMinute)
        eventBreakdown["Time"] = currentSelected
        
    else:
        #print(re.findall('[a-zA-Z]* [0-9]*, [0-9]* at [0-9][0-9]:[0-9][0-9]',line))
        continue
        #if not "DateAndTime.everyHourAt.CheckTime" in line and not "AndroidPhone.missAPhoneCall.OccuredAt" in line:
            #print("Did not find date and time")
            
            #print(re.findall('[a-zA-Z]* [0-9]* ',line))
            #print(re.findall('March 19, 2021',line))
            #exit()
        #March 19, 2021 at 02:26PM

        eventBreakdown["Time"] = datetime.datetime(eventYear,eventMonth,eventDay,eventHour,eventMinute)

    
    
    
    
    #if "You exit an area" in eventBreakdown["Triggers"]:
    #    #print(eventBreakdown["Triggers"])
    #    #print(eventBreakdown["Actions"])
    # if lineNum == :
    # print()
    structuredEvents.append(eventBreakdown)


assignUnsafeStates()
createState()


unsafeStateListLiteral = []
# print(len(structuredEvents))
# exit()
with open("CausalFile.txt",'w') as causalFile:
    for eventIndex, event in enumerate(structuredEvents):
        # if eventIndex > 50 and eventIndex < 100:
            
            
            
            # #exit()
        updateState(event,causalFile)
        #print("%d:event" % (eventIndex))
        if len(structuredEvents) > (eventIndex + 1):
            checkIfStateIsUnsafe(event,structuredEvents[eventIndex+1])
    #else:
        #checkIfStateIsUnsafe(event,None)


    
numberOfPossibleStates = 0   

serviceList = []

oldestTime = stateHistory[0]["Time"]
newestTime = stateHistory[len(stateHistory)-1]["Time"]
currentTime = oldestTime
currentState = stateHistory[0]
timeStep = datetime.timedelta(seconds=600)
stateIndexes = []
stateIDs = []
#stateList = {}
#exit()
# for stateName in state:
    
    # #print(state[stateName]["changesSimple"])
    # #print(state[stateName]["stateExtractions"])
# exit()
# for stateName in stateHistorySimpleRecord:
    
    
# exit()
#print(len(stateHistorySimpleRecord))
#simpleTrainingSpace = (len(stateHistorySimple) / 3) * 2
# with open("allStates.txt",'w') as stateFile:
    # for statePart in stateList:
        # for statePartPart in stateList[statePart]:
            # stateFile.write("\"\\\"" + statePart + "\\\"-\\\"" + statePartPart + "\\\"\"," )
# exit()
timeStepLength = int(sys.argv[3])
print("TimeSteps")
print(timeStepLength)
#simpleTrainingSpace = int(sys.argv[2]) * (10/timeStepLength)
#simpleTrainingSpace = float(sys.argv[2]) * len(stateHistorySimple)
#simpleTrainingSpace = float(sys.argv[2]) * 1440
simpleTrainingSpace = float(sys.argv[2])
evaluationSize = 2000
#simpleTrainingSpace = len(stateHistorySimple) 
traceLength = int(sys.argv[1])
limitList = int(sys.argv[5])
#stateList = ""

# for index, record in enumerate(stateHistorySimpleRecord):
    # # if index == 12:
        # 
    # if index >= 157 and 0 == 1:
        
# exit()
# oldState = ""
# differences = []
# occurancesYes = {}
# for extract in stateHistorySimple:
    
    # for part in stateExtractionsContext[int(extract[1].split(',')[1])].split(','):
        # if part in occurancesYes:
            # occurancesYes[part] += 1
        # else:
            # occurancesYes[part] = 1
# for elem in occurancesYes:
    # #print("%s:  %d" % (elem, occurancesYes[elem]))
# # for extract in stateExtractionsContext:
    # # extractSplit = extract.split(',')
    # # differences = []
    # 
    # # if oldState != "":
        # # for part1 in extractSplit:
            # # found = 0
            # # part1Split = part1.split(':')
            # # for part2 in oldState.split(','):
                # # part2Split = part2.split(':')
                # # 
                # # 
                # # 
                # # 
                # # 
                # # if part1Split[0] == part2Split[0]:
                    # # found = 1
                    # # if part1Split[1] != part2Split[1]:
                        # # differences.append(part2Split)
            # # if found == 0:
             # 
             # 
             # # exit()
             # # differences.append(part1)   
        # # #print("%d:%d" % (stateExtractionsContext.index(extract), stateExtractionsContext.index(oldState)))
        # 
        # 
    # # oldState = extract
# exit()

# if limitList == 5:
    # simpleUnsafeStates = ["14:21", "6:44"]
# elif limitList == 27:
    # simpleUnsafeStates = ["14:21", "6:44", "4:21"]
# elif limitList == 93:
    # simpleUnsafeStates =  ["14:21", "6:44", "4:21", "0:22"]
# elif limitList == 1221:
    # simpleUnsafeStates =  ["14:21", "6:44", "4:21", "0:22", "1:23"]

reduced = 1
wasWritten = 0

# for event in stateExtractionsCurrentEvent:
    
trackTime = int(sys.argv[6])
# for occuredTrack in whichOccured:
    # if whichOccured[occuredTrack] < 100:
        
        
        
# exit()
# desiredStates = ""
# for stateInfo in stateHistorySimple:
    # desiredStates = desiredStates + "\"" + stateInfo[1] + "-0\"," 



# for stateStringIndex, stateString in enumerate(overallStateExtractions):

    # fakeSplit = stateString.split('-')
    # stateStringSplit = stateExtractionsContext[int(fakeSplit[1])].split(',')
    # #transitionList[stateString] = []
    
    # for deviceIndex, deviceName in enumerate(state):
        # if deviceName == "Time":
            # continue
        # #print(state[deviceName]['stateExtractions'])
        
        # for actionNameHere in state[deviceName]['stateExtractions']:
            # totalState = state[deviceName]['state'] + '-' + actionNameHere
            # if stateStringSplit[deviceIndex].split(':')[1] == actionNameHere:
                # continue
            # alterList = stateStringSplit.copy()
            
            # #Need to use the stateExtractions from event variable since more than one device can change at once
            
            # 
            # 
            # # print(len(alterList))
            # 
            # alterList[deviceIndex] = actionNameHere
            # # print(stateExtractionsContext[int(fakeSplit[1])])
            # 
            # # print(','.join(alterList))
            
            
            # # print(actionNameHere in stateExtractionsCurrentEvent)
            # # print(','.join(alterList) in stateExtractionsContext)
            # #print(stateExtractionsCurrentEvent.index(actionNameHere) + '-' + stateExtractionsContext[','))
            # 

            # if actionNameHere in stateExtractionsCurrentEvent and ','.join(alterList) in stateExtractionsContext and (str(stateExtractionsCurrentEvent.index(actionNameHere)) + '-' + str(stateExtractionsContext.index(','.join(alterList)))) in overallStateExtractions:
                # #transitionList[stateString].append((str(stateExtractionsCurrentEvent.index(actionNameHere)) + '-' + str(stateExtractionsContext.index(','.join(alterList)))))
                # transitionList[fakeSplit[1]][str(stateExtractionsContext.index(','.join(alterList))))


newlyDiscovered = 0
alreadyHad = 0
notAvailables = 0

for conIndex, contextName in enumerate(stateExtractionsContext):
    continue
    for evenIndex, eventName in enumerate(stateExtractionsCurrentEvent):
        
        if not str(evenIndex) in transitionList[str(conIndex)]:
           contextSplit = contextName.split(',')
           eventSplit = eventName.split(',')
           for eventPart in eventSplit:
            eventPartSplit = eventPart.split(':')
            for contextPartIndex, contextPart in enumerate(contextSplit):
                if contextPart.split(':')[0] == eventPartSplit[0]:
                    contextSplit[contextPartIndex] = ':'.join(eventPartSplit)
           contextString = ','.join(contextSplit)

           if contextString in stateExtractionsContext:
            newlyDiscovered += 1
            transitionList[str(conIndex)][str(evenIndex)] = str(stateExtractionsContext.index(contextString))
            transitionList[str(conIndex)][str(stateExtractionsContext.index(contextString)) + '-c'] = str(evenIndex)
            if not str(stateExtractionsContext.index(contextString)) in validTargetsList[str(conIndex)]:
                validTargetsList[str(conIndex)].append(str(stateExtractionsContext.index(contextString)))
           #else:
            #transitionList[str(conIndex)][str(evenIndex)] = "N/A"
        else:
            alreadyHad += 1
# print(len(stateExtractionsCurrentEvent))

# for transitionElement in transitionList:
    
    # for newElem in transitionList[transitionElement]:
        
    
    # print(len(transitionList[transitionElement]))
    # exit()
with open("/home/man5336/Documents/ProvPredictor/EvalFolder/allowedTransitions.txt", "wb") as myFile:
            pickle.dump(transitionList, myFile)
with open("/home/man5336/Documents/ProvPredictor/EvalFolder/permittedTargets.txt", "wb") as myFile:
            pickle.dump(validTargetsList, myFile)








mf = pd.read_csv("traceOutput.csv")
dataFile = open("traceOutput.csv", "r")
dataList = list(dataFile)
deviceNames = dataList[0].split(",")
deviceNames[len(deviceNames) - 1] = deviceNames[len(deviceNames) - 1][:-1]
linkedDevices = []
simpleList = {}
for index1, device1 in enumerate(deviceNames):
    simpleList[index1] = [[index1], [],[]]
samples = []

temp = []
tests = []
#print(test[4][0]['ssr_ftest'][1])
maxLag = 0
necessaryDevices = []
for index1, device1 in enumerate(deviceNames):
    
    testTracker = []
    tempList = []
    minSignificance = 0.055
    while len(tempList) == 0:
        minSignificance -= 0.005
        for index2, device2 in enumerate(deviceNames):
            if index1 != index2:
                try:
                    with suppress_stdout_stderr():
                        test = grangercausalitytests(mf[[device1, device2]], maxlag=5)
                except:
                    continue
                lastViable = -1
                for testVal in test:
                    if test[testVal][0]['ssr_ftest'][0] >= 5:
                        lastViable = testVal
                    else:
                        break
                    #print("%d : %f" % (testVal,test[testVal][0]['ssr_ftest'][0]))
                # lastViables.append(lastViable)
                # if lastViable == -1:
                    
                    # exit()
                if lastViable > maxLag:
                    maxLag = lastViable
                if lastViable != -1 and float(test[lastViable][0]['ssr_ftest'][1]) <= minSignificance:# or (index1 == 1 and index2 == 3) or (index1 == 3 and index2 == 1):
                    #linkedDevices.append([index2, index1, test[lastViable][0]['ssr_ftest'][1]])
                    testTracker.append(float(test[lastViable][0]['ssr_ftest'][1]))
                    tempList.append([index2,float(test[lastViable][0]['ssr_ftest'][1])])
                    #simpleList[index1][0].append(index2)
                    stringToPrint = deviceNames[index2] + str(float(test[lastViable][0]['ssr_ftest'][1]))
                    
                    #simpleList[index1][0].append([deviceNames[index2],test[lastViable][0]['ssr_ftest'][1]])
        
    if len(testTracker) > 7:
 
        simpleList[index1][0] = [index1]
        testTracker.sort()
        testTracker = testTracker[-7:]
    for value in tempList:
        if value[1] in testTracker:
            simpleList[index1][0].append(value[0])
            if (index1 == 23 or index1 == 24 or index1 == 25 or index1 == 26) and not deviceNames[value[0]] in necessaryDevices:
                necessaryDevices.append(deviceNames[value[0]])
            linkedDevices.append([value[0], index1, value[1]])
    simpleList[index1][0].sort()

                #simpleList[index1][0].append([deviceNames[index2],test[lastViable][0]['ssr_ftest'][1]])

# for deviceIndexThing in simpleList:
    
    
    # for relDevIn in simpleList[deviceIndexThing][0]:
        
        
# exit()
    

#print(necessaryDevices)
splitStart = -1
splitEnd = -1
if sys.argv[7] != '-1':
    splitStart = int((float(sys.argv[7])/100) * len(simpleUnsafeStates))
    splitEnd = splitStart + 100
unseenToDo = sys.argv[8]

unseenTracker = []
happenedTracker = {}
unsafeToNotUse = []
while reduced == 1:
    #with open("unsafeStateFile.csv", 'w') as unsafeFile:
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/unsafeStateFile.csv", 'w') as unsafeFile:
        with open("/home/man5336/Documents/ProvPredictor/EvalFolder/unsafeStateTranslations.txt", "wb") as myFile:
            pickle.dump(unsafeStates, myFile)
            writeline = ""
            # ocurranceFaultTracker = {}
            # for stateToWrite in stateHistorySimple:
                # if int(stateToWrite[1].split(":")[0]) == limitList:
                    # if stateToWrite[1] in ocurranceFaultTracker:
            # for stateToWrite in stateHistorySimple:
                # if int(stateToWrite[1].split(":")[0]) == limitList:
                    # writeline = writeline + stateToWrite[1] + ","
            # unsafeFile.write(writeline[:-1] + "\n")
            #print(simpleUnsafeStates)
            if trackTime == 1:
                toWrite = ""
                for unsafeIndex, unsafeStateToWrite in enumerate(simpleUnsafeStates):  
                    # if not int(unsafeStateToWrite.split(":")[0]) == limitList:
                        # continue
                    
                    # for minute in range(61):
                        # toWrite = toWrite + str(unsafeStateToWrite) + ":" + str(minute) + ","
                    unsafeSplit = unsafeStateToWrite.split('-')
                    
                    if not unsafeSplit[2] in happenedTracker:
                        happenedTracker[unsafeSplit[2]] = 0
                    happenedTracker[unsafeSplit[2]] += 1
                    if unsafeSplit[2] == unseenToDo and not unsafeSplit[2] in unsafeToNotUse:
                        unsafeToNotUse.append(unsafeSplit[1])
                    timeString = ""
                    reasonsString = ""
                    #for timeCheckIndex, timeCheck in enumerate(simpleUnsafeStates[unsafeStateToWrite]):
                    if len(simpleUnsafeStates[unsafeStateToWrite][0]) > 0:
                        timeString = timeString + '-' + simpleUnsafeStates[unsafeStateToWrite][0][0]
                    else:
                        timeString = timeString + '-00:00/23:59'

                    for reasonIndex, reasons in  enumerate(simpleUnsafeStates[unsafeStateToWrite][1]):
                            reasonsString = reasonsString + '-' + reasons
                    # if int(unsafeSplit[1]) >= 22:
                        # if unsafeSplit[2] == '0':
                            # unsafeSplit[2] = '2'
                        # if unsafeSplit[2] == '1':
                            # unsafeSplit[2] = '3'
                        # unsafeStateToWrite = '-'.join(unsafeSplit)
                    #if unsafeSplit[2] == unseenToDo and not unsafeSplit[1] in unseenTracker:
                     #   unseenTracker.append()
                     
                    toWrite = toWrite + unsafeStateToWrite  + timeString +  reasonsString + ',' 
                    
                    #unsafeFileTranslate.write("Start\n")
                    #unsafeFileTranslate.write(unsafeSplit[0] + '-' + unsafeSplit[1] + '\n')
                    

                    # for part in unsafeStates[int(unsafeSplit[2])]:
                        # initialArray = ""
                        # for part2Index, part2 in enumerate(unsafeStates[int(unsafeSplit[2])][part][0]):
                            # if part2Index != 0:
                                # initialArray += "-"
                            # initialArray += part2
                    # exit()
                    #toWrite = toWrite + str(unsafeStateToWrite[0]) + ","
                toWrite = toWrite[:-1]
                unsafeFile.write(toWrite + "\n")
            else:
                toWrite = ""
                for unsafeIndex, unsafeStateToWrite in enumerate(simpleUnsafeStates):  
                    # if not int(unsafeStateToWrite.split(":")[0]) == limitList:
                        # continue
                    if wasWritten != 0:
                        toWrite = toWrite + ","
                    
                    wasWritten = 1
                    toWrite = toWrite + str(unsafeStateToWrite)
                unsafeFile.write(toWrite + "\n")

            for elemIndex, elem in enumerate(limitedActionList):
                lineToWrite = "" + elem + "," #+ str(elemIndex)
                for index, action in enumerate(limitedActionList[elem]):
                   lineToWrite = lineToWrite + action + ":"
                unsafeFile.write(lineToWrite[:-1] + "\n")
    measureTime = 0
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/eventTranslations.txt", "wb") as myFile:
        pickle.dump(stateExtractionsCurrentEvent, myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/contextTranslations.txt", "wb") as myFile:
        #pickle.dump(stateExtractionsContextDict, myFile)
        pickle.dump(stateExtractionsContext, myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/durationRecords.txt", "wb") as myFile:
        pickle.dump(simpleDurationsTracker, myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/timeRecords.txt", "wb") as myFile:
        pickle.dump(simpleTimeTracker, myFile)

    
    startingHour = int(str(stateHistorySimple[0][-1].hour))
    startingMinute = int(str(stateHistorySimple[0][-1].minute))
    with open("vocabSizeTracker.txt", 'a') as trackerFile:
        trackerFile.write(str(len(overallStateExtractions)) + "\n")
    with open("vocabFileContext.vocab", 'w') as vocabFile:
    #with open("vocabFileContext.vocab", 'w') as vocabFile:
        for record in overallStateExtractions:
        #for record in stateExtractionsContext:
            vocabFile.write("<" + record + ">\n")
    with open("vocabFileTime.vocab", 'w') as vocabFile:        
    #with open("vocabFileTime.vocab", 'w') as vocabFile:
        for hour in range(24):
            #for minute in range(60):
                for record in overallStateExtractions:
                    #vocabFile.write("<" + record.split('-')[0] + "-" + str(hour) + ':' + str(minute) + ">\n")
                    vocabFile.write("<" + record.split('-')[0] + "-" + str(hour) + ">\n")

            
    #totalSteps = 0
    stateOccurances = {}
    transitionMap = {}
    modelDict = {}
    deviceNamesHere = []
    for deviceIndex, device in enumerate(state):
        deviceNamesHere.append(device)
    
    stateNumTracker = 0
    eventNumTracker = 0
    
    for deviceIndex, device in enumerate(state):
        #print(deviceIndex)
        if device == "Time":
            continue
        with open("checkIfTimeIsRelevant.csv", 'w') as trainingFile:
          with open("checkIfTimeIsRelevant2.csv", 'w') as trainingFile2:
            oldState = ""
            currentLine = ""
            trainingFile.write(str(device) + ',Time\n')
            trainingFile2.write(str(device) + ',Time\n')
            measureTime = 0
            for stateIndex, stateToWrite in enumerate(stateHistorySimple):
                    #print(stateExtractionsContext[int(stateToWrite[1].split('-')[1])].split(',')[deviceIndex])
                if stateIndex == 0:
                    startingHour = int(str(stateToWrite[-1].hour))
                    startingMinute = int(str(stateToWrite[-1].minute))
                stateContext = stateExtractionsContext[int(stateToWrite[1].split('-')[1])].split(',')
                
                if oldState == "" or oldState != stateContext[deviceIndex]:
                    trainingFile.write(str(stateList[device].index(stateContext[deviceIndex].split(':')[1])) + "," + str(startingHour) + "\n")
                    trainingFile2.write(str(stateList[device].index(stateContext[deviceIndex].split(':')[1])) + "," + str(startingMinute) + "\n")
                #oldState = str(stateToWrite[1].split('-')[1])
                oldState = stateContext[deviceIndex]
                # if not "hour" in stateExtractionsContext[int(stateToWrite[1].split('-')[1])].split(',')[deviceIndex]:
                    
                    
                    # print(str(stateList[device].index(stateContext[deviceIndex].split(':')[1])))
                    # print(stateHistorySimple[stateIndex + 1])
                    # exit()
                #A bad way to do states that occur concurrently
                if stateIndex + 1 != len(stateHistorySimple) and stateHistorySimple[stateIndex + 1][0] == stateToWrite[0]:
                    continue

                firstInstance = 1
                writeHour = 1
                #if stateIndex < simpleTrainingSpace:

                #if measureTime < simpleTrainingSpace:
                if stateIndex < simpleTrainingSpace:
                    eventNumTracker += 1
                    largestIndex = measureTime
                    if writeHour == 1:
                        writeHour = 0
                    while measureTime <= stateToWrite[0]:
                        measureTime += timeStepLength
                        startingMinute += timeStepLength
                        if not startingMinute > 60:
                            trainingFile2.write(str(stateList[device].index(stateContext[deviceIndex].split(':')[1])) + "," + str(startingMinute) + "\n")
                        if startingMinute >= 60:
                            startingMinute = 0
                            trainingFile2.write(str(stateList[device].index(stateContext[deviceIndex].split(':')[1])) + "," + str(startingMinute) + "\n")
                            startingHour += 1
                            if startingHour == 24:
                                    startingHour = 0
                                    writeHour = 1
                            trainingFile.write(str(stateList[device].index(stateContext[deviceIndex].split(':')[1])) + "," + str(startingHour) + "\n")
                            
                       
        mf = pd.read_csv("checkIfTimeIsRelevant.csv")
        mf2 = pd.read_csv("checkIfTimeIsRelevant2.csv")
        try:
            with suppress_stdout_stderr():
                test = grangercausalitytests(mf[[device, "Time"]], maxlag=5)
        except:
            None
        try:
            with suppress_stdout_stderr():
                test2 = grangercausalitytests(mf2[[device, "Time"]], maxlag=5)
        except:
            print("Why here?")
            None
        lastViable = -1
      
        
        for testVal in test:
            
            if test[testVal][0]['ssr_ftest'][0] >= 5:
                lastViable = testVal
            else:
                break
       
        if lastViable > maxLag:
            maxLag = lastViable

            if lastViable != -1 and float(test[lastViable][0]['ssr_ftest'][1]) <= 0.05:# or (index1 == 1 and index2 == 3) or (index1 == 3 and index2 == 1):
                #simpleList[deviceIndex][1] = 1
                with open("checkIfTimeIsRelevant.csv",'r') as timeFile:
                    timeList = list(timeFile)
                    chiHourTracker = {}
                    timeTrackerChi = {}
                    previousLine = ""
                    for lineIndex, line in enumerate(timeList):
                        line = line.replace('\n','')
                        lineSplit = line.split(',')
                        if lineIndex == 0:
                            continue
                        if lineIndex == 1:
                            previousLine = lineSplit
                            continue
                        lineSplit = line.split(',')
                        deviceValue = lineSplit[0]
                        timeValue = previousLine[1]
                        if not deviceValue in chiHourTracker:
                            chiHourTracker[deviceValue] = [0,{}]
                        if not timeValue in timeTrackerChi:
                            timeTrackerChi[timeValue] = 0
                        timeTrackerChi[timeValue] += 1
                        if not timeValue in chiHourTracker[deviceValue][1]:
                            chiHourTracker[deviceValue][1][timeValue] = 0
                        chiHourTracker[deviceValue][0] += 1
                        chiHourTracker[deviceValue][1][timeValue] += 1
                        previousLine = lineSplit
                    for deviceValue in chiHourTracker:
                        for timeValue in chiHourTracker[deviceValue][1]:
                            expectedValue = (chiHourTracker[deviceValue][0]*timeTrackerChi[timeValue])/len(timeList)
                            if (abs(chiHourTracker[deviceValue][1][timeValue] - expectedValue)**2)/expectedValue < 0.05 and not timeValue in simpleList[deviceIndex][1]:
                                simpleList[deviceIndex][1].append(timeValue)


            
        lastViable = -1
        for testVal in test2:
            if test2[testVal][0]['ssr_ftest'][0] >= 5:
                lastViable = testVal
            else:
                break

        if lastViable > maxLag:
            maxLag = lastViable
        if lastViable != -1 and float(test2[lastViable][0]['ssr_ftest'][1]) <= 0.05:# or (index1 == 1 and index2 == 3) or (index1 == 3 and index2 == 1):
            # if simpleList[deviceIndex][1] == 1:
                # simpleList[deviceIndex][1]  = 3
            # else:
                # simpleList[deviceIndex][1]  = 2
            with open("checkIfTimeIsRelevant2.csv",'r') as timeFile:
                timeList = list(timeFile)
                chiMinuteTracker = {}
                timeTrackerChi = {}
                previousLine = ""
                for lineIndex, line in enumerate(timeList):
                    line = line.replace('\n','')
                    lineSplit = line.split(',')
                    if lineIndex == 0:
                        continue
                    if lineIndex == 1:
                        previousLine = lineSplit
                        continue
                    lineSplit = line.split(',')
                    deviceValue = lineSplit[0]
                    timeValue = previousLine[1]
                    if not deviceValue in chiMinuteTracker:
                        chiMinuteTracker[deviceValue] = [0,{}]
                    if not timeValue in timeTrackerChi:
                        timeTrackerChi[timeValue] = 0
                    timeTrackerChi[timeValue] += 1
                    if not timeValue in chiMinuteTracker[deviceValue][1]:
                        chiMinuteTracker[deviceValue][1][timeValue] = 0
                    chiMinuteTracker[deviceValue][0] += 1
                    chiMinuteTracker[deviceValue][1][timeValue] += 1
                    previousLine = lineSplit
                for deviceValue in chiMinuteTracker:
                    for timeValue in chiMinuteTracker[deviceValue][1]:
                        expectedValue = (chiMinuteTracker[deviceValue][0]*timeTrackerChi[timeValue])/len(timeList)
                        if (abs(chiMinuteTracker[deviceValue][1][timeValue] - expectedValue)**2)/expectedValue < 0.05 and not timeValue in simpleList[deviceIndex][2]:
                            simpleList[deviceIndex][2].append(timeValue)
               #Time needs to be refined so that its for each event not overall device
    #print(maxLag)

    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/simpleListTemp.txt", "wb") as myFile:
            pickle.dump(simpleList, myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/dataListTemp.txt", "wb") as myFile:
            pickle.dump(dataList, myFile)
    print(maxLag)
    # with open("/home/man5336/Documents/ProvPredictor/EvalFolder/simpleListTemp.txt", "rb") as myFile:
            # simpleList = pickle.load(myFile)
    # with open("/home/man5336/Documents/ProvPredictor/EvalFolder/dataListTemp.txt", "rb") as myFile:
            # dataList = pickle.load(myFile)
    chiSquareResults = chiSquareTimeWindow(simpleList,maxLag,dataList)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/chiSquareTemp.txt", "wb") as myFile:
            pickle.dump(chiSquareResults, myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/stateTemp.txt", "wb") as myFile:
            pickle.dump(state, myFile)
    # with open("/home/man5336/Documents/ProvPredictor/EvalFolder/chiSquareTemp.txt", "rb") as myFile:
            # chiSquareResults = pickle.load(myFile)
    # with open("/home/man5336/Documents/ProvPredictor/EvalFolder/stateTemp.txt", "rb") as myFile:
            # state = pickle.load(myFile)
    necessaryHistories = []
    predicateList = {}
    dependencyTracker = {}
    overallPredicates = {}
    overallPredicates["total"] = 0
    overallPredicates["otherTotals"] = {}
    for deviceIndex, device in enumerate(state):
        if device == "Time":
            continue    
        #Creating state set
        for stateNameHere in state[deviceNamesHere[deviceIndex]]["stateExtractions"]:
            dependencyTracker[stateNameHere] = []
            if not stateNameHere in overallPredicates:
                    overallPredicates[stateNameHere] = 0
            vocabList = []
            vocabListTemp = []
            singleVocabList = []
            predicateList[stateNameHere] = {"predicates": {}, "notDefinitions": {}}
            #print(chiSquareResults[deviceNamesHere[deviceIndex] + ":" + stateNameHere])
            for relevantIndex, relevantStateDevice in enumerate(chiSquareResults[stateNameHere]):
                for stateValue in chiSquareResults[stateNameHere][relevantStateDevice]:
                    singleVocabList.append(state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)])
                if vocabList == []:
                    stateValueTotal = []
                    for stateValue in chiSquareResults[stateNameHere][relevantStateDevice]:
                        vocabList.append(state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)])
                        stateValueTotal.append(state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)])
                    
                    
                    if not len(stateValueTotal) >= len(state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"]): 
                        vocabList.append(deviceNamesHere[int(relevantStateDevice)] + ":" + "NOT")
                        predicateList[stateNameHere]["notDefinitions"][deviceNamesHere[int(relevantStateDevice)]] = stateValueTotal.copy()
                else:
                    stateValueTotal = []
                    for oldValue in vocabList:
                        #for stateValue in state[deviceNamesHere[deviceIndexTemp]]["stateExtractions"]:
                        
                        for stateValue in chiSquareResults[stateNameHere][relevantStateDevice]:
                            if not state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)] in stateValueTotal:
                                stateValueTotal.append(state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)])
                            vocabListTemp.append(oldValue + ',' + state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)])
                            dependencyTracker[stateNameHere].append(state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)])
                            if relevantIndex == (len(chiSquareResults[stateNameHere]) - 1) and  not oldValue + ',' + state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)] in predicateList[stateNameHere]["predicates"]:
                                #if not  'NOT' in oldValue + ',' + state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)]: 
                                predicateList[stateNameHere]["predicates"][oldValue + ',' + state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)]] = []
                                #else:
                                #    predicateList[stateNameHere]["nots"][oldValue + ',' + state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)]] = []
                    if not len(stateValueTotal) >= len(state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"]): 
                        for oldValue in vocabList:
                            vocabListTemp.append(oldValue + ',' + deviceNamesHere[int(relevantStateDevice)] + ":" + "NOT")
                            if relevantIndex == (len(chiSquareResults[stateNameHere]) - 1):
                                predicateList[stateNameHere]["predicates"][oldValue + ',' + deviceNamesHere[int(relevantStateDevice)] + ":" + "NOT"] = []
                        predicateList[stateNameHere]["notDefinitions"][deviceNamesHere[int(relevantStateDevice)]] = stateValueTotal.copy()
                        
                    vocabList = vocabListTemp.copy()
                    vocabListTemp = []
            # if deviceIndex == 3 and stateNameHere == "Magic Hue:Turn on lights":
    predicatesToUpdate = {}
    #print(predicateList["soil_sensor1_vwc:0.987"])
    #For now, coding for simple probability
    # print(len(predicateList))
    for predicateIndex, predicateName in enumerate(predicateList):
      # print(predicateIndex)
      # print(predicateName)
      # print(len(predicateList[predicateName]["predicates"]))
      # print()
      for predicate in predicateList[predicateName]["predicates"]:
        predicateSplit = predicate.split(',')
        #necessaryDependencies = []
        independent = 1
        for predicateIndex1, predicatePart1 in enumerate(predicateSplit):
            if "NOT" in predicatePart1:
                predicateList[predicateName]["predicates"][predicate].append(predicatePart1)
                continue
            if not predicatePart1 in overallPredicates:
                    overallPredicates[predicatePart1] = 0
            predicatesToUpdate[predicatePart1] = []
            for predicateIndex2, predicatePart2 in enumerate(predicateSplit):
                if predicateIndex1 == predicateIndex2 or "NOT" in predicatePart2:
                    continue
                if predicatePart2 in dependencyTracker[predicatePart1]:
                    independent = 0
                    predTemp1 = predicatePart1
                    predTemp2 = predicatePart2
                    if predicatePart2.split(":")[0] +',' + predicatePart1.split(":")[0] in overallPredicates["otherTotals"]:
                        predTemp1 = predicatePart2
                        predTemp2 = predicatePart1
                    predicateList[predicateName]["predicates"][predicate].append(predTemp1 +',' + predTemp2)
                    predicatesToUpdate[predicatePart1].append(predicatePart2)
                    if not predTemp1 +',' + predTemp2 in overallPredicates["otherTotals"]:
                        overallPredicates[predTemp1 +',' + predTemp2] = 0
                        if not predTemp1.split(":")[0] +',' + predTemp2.split(":")[0]  in overallPredicates["otherTotals"]:
                            overallPredicates["otherTotals"][predTemp1.split(":")[0] +',' + predTemp2.split(":")[0]] = 0
                        
            if independent == 1:
                predicateList[predicateName]["predicates"][predicate].append(predicatePart1)
               
     



    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/deleteableState.txt", "wb") as myFile:
            pickle.dump(state, myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/deleteableStateExtractionsContext.txt", "wb") as myFile:
            pickle.dump(stateExtractionsContext, myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/deleteableState.txt", "wb") as myFile:
            pickle.dump(state, myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/deleteableStateHistorySimple.txt", "wb") as myFile:
            pickle.dump(stateHistorySimple, myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/deleteableUnsafeToNotUse.txt", "wb") as myFile:
            pickle.dump(unsafeToNotUse, myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/deleteableChiSquareResults.txt", "wb") as myFile:
            pickle.dump(chiSquareResults, myFile)
    with open("linkRecords.csv",'w') as linkRecordFile:
        linkRecordFile.write("")
    for deviceIndex, device in enumerate(state):
        #print(deviceIndex)
        if device == "Time":
            continue    
        #Creating state set
        necessaryHistoryTracker = []
        
        for stateNameHere in state[deviceNamesHere[deviceIndex]]["stateExtractions"]:
            dependencyTracker[stateNameHere] = []
            vocabList = []
            vocabListTemp = []
            singleVocabList = []
            #print(chiSquareResults[deviceNamesHere[deviceIndex] + ":" + stateNameHere])
            with open("linkRecords.csv",'a') as linkRecordFile:
                linkRecordFile.write("" + stateNameHere)
                print(stateNameHere)
                print(chiSquareResults[stateNameHere])
                for relevantIndex, relevantStateDevice in enumerate(chiSquareResults[stateNameHere]):
                    linkRecordFile.write("\n" + deviceNamesHere[int(relevantStateDevice)])
                    
                    for stateValue in chiSquareResults[stateNameHere][relevantStateDevice]:
                        singleVocabList.append(state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)])
                        linkRecordFile.write("," + state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)])
                    if vocabList == []:
                        stateValueTotal = []
                        for stateValue in chiSquareResults[stateNameHere][relevantStateDevice]:
                            vocabList.append(state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)])
                            stateValueTotal.append(state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)])
                        vocabList.append(deviceNamesHere[int(relevantStateDevice)] + ":" + "NOT")
                    else:
                        stateValueTotal = []
                        for oldValue in vocabList:
                            #for stateValue in state[deviceNamesHere[deviceIndexTemp]]["stateExtractions"]:
                            
                            for stateValue in chiSquareResults[stateNameHere][relevantStateDevice]:
                                if not state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)] in stateValueTotal:
                                    stateValueTotal.append(state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)])
                                vocabListTemp.append(oldValue + ',' + state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)])
                                dependencyTracker[stateNameHere].append(state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)])
                                    #else:
                                    #    predicateList[stateNameHere]["nots"][oldValue + ',' + state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"][int(stateValue)]] = []
                        if not len(stateValueTotal) >= len(state[deviceNamesHere[int(relevantStateDevice)]]["stateExtractions"]): 
                            for oldValue in vocabList:
                                vocabListTemp.append(oldValue + ',' + deviceNamesHere[int(relevantStateDevice)] + ":" + "NOT")
                        vocabList = vocabListTemp.copy()
                        vocabListTemp = []      
                linkRecordFile.write("\n\n\n")
            #exit()
            if len(simpleList[deviceIndex][1]) > 0:
                vocabListTemp = []
                for oldValue in vocabList:
                    for time in simpleList[deviceIndex][1]:
                            vocabListTemp.append(oldValue + ',Hour:' + str(time))
                    vocabListTemp.append(oldValue + ',Hour:NOT' )
                vocabList = vocabListTemp.copy()
                vocabListTemp = []
            if len(simpleList[deviceIndex][2]) > 0:
                vocabListTemp = []
                for oldValue in vocabList:
                    for time in simpleList[deviceIndex][2]:
                            vocabListTemp.append(oldValue + ',Minute:' + str(time))
                    vocabListTemp.append(oldValue + ',Minute:NOT' )
                vocabList = vocabListTemp.copy()
                vocabListTemp = []
            with open("tempVocabFile.vocab", 'w') as vocabFile:
                for vocIndex, vocabPart in enumerate(vocabList):
                    if vocIndex != 0:
                        vocabFile.write("\n")
                    #vocabFile.write("<" + vocabPart + ">")
                    vocabFile.write("<" + str(vocIndex) + ">")
            changesTracker = 0
            
            with open("/home/man5336/Documents/ProvPredictor/EvalFolder/deleteableVocabList.txt", "wb") as myFile:
                pickle.dump(vocabList, myFile)
            
                
            
            notUsed = vocabList.copy()
            with open("tempTrainingFile.train", 'w') as trainingFile:
                with open("tempTrainingFileNoSelfs.train", 'w') as trainingFile2:
                
                    oldState = ""
                    currentLine = ""
                    currentLine2 = ""
                    
                    measureTime = 0
                    oldStateString = ""
                    for stateIndex, stateToWrite in enumerate(stateHistorySimple):
                        oneWrite = 0
                        
                        if stateToWrite[1].split('-')[1] in unsafeToNotUse:
                            currentLine = currentLine + '\n'
                            currentLine2 = currentLine2 + '\n'
                            continue
                        if stateIndex == 0:
                            startingHour = int(str(stateToWrite[-1].hour))
                            startingMinute = int(str(stateToWrite[-1].minute))
                        stateContext = stateExtractionsContext[int(stateToWrite[1].split('-')[1])].split(',')
                        stateString = ""
                        stateStringNoTime = ""
                        # if deviceIndex == 18:
                            # print(chiSquareResults[stateNameHere])
                        for relevantDevice in chiSquareResults[stateNameHere]:
                            if stateStringNoTime != "":
                                stateStringNoTime += ","
                            # print(relevantDevice)
                            # print(stateContext[int(relevantDevice)])
                            # print(chiSquareResults[stateNameHere][relevantDevice])
                            # print(state[stateContext[int(relevantDevice)].split(":")[0]]["stateExtractions"])
                            # print()
                            if str(state[stateContext[int(relevantDevice)].split(":")[0]]["stateExtractions"].index(stateContext[int(relevantDevice)])) in chiSquareResults[stateNameHere][relevantDevice]:
                                stateStringNoTime += stateContext[int(relevantDevice)]
                            else:
                                stateStringNoTime += stateContext[int(relevantDevice)].split(":")[0] + ":NOT"
                        stateString = stateStringNoTime
                        if len(simpleList[deviceIndex][1]) > 0:
                            if startingHour in simpleList[deviceIndex][1]:
                                stateString += "," + str(startingHour)
                            else:
                                stateString += ",Hour:NOT"
                        if len(simpleList[deviceIndex][2]) > 0:
                            if startingMinute in simpleList[deviceIndex][1]:
                                stateString += "," + str(startingMinute)
                            else:
                                stateString += ",Minute:NOT"
                                
                        if oldStateString != "" and oldStateString == str(vocabList.index(stateString)):
                            oneWrite = 1
                        oldState = str(stateToWrite[1].split('-')[1])
                        
                        #A bad way to do states that occur concurrently
                        # if stateIndex + 1 != len(stateHistorySimple) and stateHistorySimple[stateIndex + 1][0] == stateToWrite[0]:
                            # continue

                        firstInstance = 1
                        writeHour = 1
                        #if stateIndex < simpleTrainingSpace:
                        if splitStart == -1:
                            #if measureTime < simpleTrainingSpace:
                            if stateIndex < simpleTrainingSpace:
                                largestIndex = measureTime
                                if writeHour == 1:
                                    writeHour = 0
                                while measureTime <= stateToWrite[0]:
                                    currentLine = currentLine + "<" + str(vocabList.index(stateString)) + "> "
                                    if oneWrite == 0:
                                        oneWrite = 1
                                        currentLine2 = currentLine2 + "<" + str(vocabList.index(stateString)) + "> "
                                        if stateString in notUsed:
                                            del notUsed[notUsed.index(stateString)]
                                        changesTracker += 1
                                        oldStateString = str(vocabList.index(stateString))
                                        
                                        
                                        
                                        # print(str(vocabList.index(stateString)))
                                    measureTime += timeStepLength
                                    startingMinute += timeStepLength
                                    if startingMinute >= 60:
                                        startingMinute = 0
                                        startingHour += 1
                                        if simpleList[deviceIndex][1] == 1:
                                            stateString = stateStringNoTime + "," + str(startingHour)
                                        if startingHour == 24:
                                                startingHour = 0
                                                writeHour = 1
                        else:    
                            if measureTime < splitStart:
                                largestIndex = measureTime
                                if writeHour == 1:
                                    writeHour = 0
                                while measureTime <= stateToWrite[0]:
                                    
                                    currentLine = currentLine + "<" + str(vocabList.index(stateString)) + "> "
                                    if oneWrite == 0:
                                        oneWrite = 1
                                        
                                        
                                        
                                        # print(str(vocabList.index(stateString)))
                                        
                                        oldStateString = str(vocabList.index(stateString))
                                        currentLine2 = currentLine2 + "<" + str(vocabList.index(stateString)) + "> "
                                        changesTracker += 1
                                    measureTime += timeStepLength
                                    startingMinute += timeStepLength
                                    if startingMinute >= 60:
                                        startingMinute = 0
                                        startingHour += 1
                                        if simpleList[deviceIndex][1] == 1:
                                            stateString = stateStringNoTime + "," + str(startingHour)
                                        if startingHour == 24:
                                                startingHour = 0
                                                writeHour = 1
                                if not measureTime < splitStart:
                                    currentLine = currentLine + "\n"
                                    currentLine2 = currentLine2 + "\n"
                            elif measureTime > splitEnd:
                                largestIndex = measureTime
                                if writeHour == 1:
                                    writeHour = 0
                                while measureTime <= stateToWrite[0]:
                                    currentLine = currentLine + "<" + str(vocabList.index(stateString)) + "> "
                                    if oneWrite == 0:
                                        oneWrite = 1
                                        oldStateString = str(vocabList.index(stateString))
                                        currentLine2 = currentLine2 + "<" + str(vocabList.index(stateString)) + "> "
                                        changesTracker += 1
                                    measureTime += timeStepLength
                                    startingMinute += timeStepLength
                                    if startingMinute >= 60:
                                        startingMinute = 0
                                        startingHour += 1
                                        if simpleList[deviceIndex][1] == 1:
                                            stateString = stateStringNoTime + "," + str(startingHour)
                                        if startingHour == 24:
                                                startingHour = 0
                                                writeHour = 1
                    trainingFile.write(currentLine)
                    trainingFile2.write(currentLine2)
                    if len(notUsed) > 0:
                        for toAdd in notUsed:
                            trainingFile2.write("<" + str(vocabList.index(toAdd)) + "> ")
            if changesTracker < 6:
                continue
            vocab_file = "tempVocabFile.vocab"
            order =  3
            training_file = "tempTrainingFile.train"
            op = ['-v', vocab_file, '-o', str(order), '-s', "ModKN"]
            mitlmi = ['estimate-ngram', '-t', training_file, '-wl', 'ilmContext','-verbose','0']
            mitlmi.extend(op)
            validGraph = 1
            try:
                subprocess.check_output(mitlmi)
            except (subprocess.CalledProcessError, FileNotFoundError) as e:
                print(stateNameHere)
                print(vocabList)
                #print(currentLine)
                print("1")
                print()
                #sys.stderr.write(repr(e) + "\n1\n")
                validGraph = 0
                #sys.exit(1) 
            ngram_cp_storePredicates = [-1]
            if validGraph == 1:
             ngram_cp_storePredicates = {"Base": {}}
             with open("ilmContext", 'r') as f: 
                  arpa_model_header = []
                  ngram_bucketsSelf = []
                  ngram_bw_store = {}
                  distribution = {}
                  next(f) # skip 1st line
                  next(f) # skip 2nd line
                  bucketDivide = 0
                  for line in f:
                    if not line.strip():
                      break
                    arpa_model_header.append(int(line.strip().split('=')[-1]))

                  for bucket in range(len(arpa_model_header)):
                    next(f) # skip r'\\\d+-grams:'
                    ngram_cp_store = defaultdict(list) if bucket else {}
                    
                    for line in f:
                      if not line.strip():
                        break
                      historyCalc = line.strip().replace('<','').replace('>','').split('\t')[1].split(' ')
                      target = 0
                      if 's' in historyCalc or '/s' in historyCalc:
                        continue
                      #Commented out, removed self-transitions
                      predicatesHere = []
                      if len(historyCalc) == 1:
                        if line.count('<') > 1:
                            historyCalc = line.strip().split('>')[0].replace('<','').replace('>','').split('\t')[1].split(' ')
                        target = vocabList[int(historyCalc[-1])].split(',')[0]
                        if vocabList[int(historyCalc[-1])] in predicateList[stateNameHere]["predicates"]:
                            predicatesHere = predicateList[stateNameHere]["predicates"][vocabList[int(historyCalc[-1])]].copy()
                        else:
                            predicatesHere = []
                        if not target in predicatesHere:
                            predicatesHere.append(target)
                        for vocabElemIndex, vocabElem in enumerate(vocabList[int(historyCalc[-1])].split(',')):
                            if vocabElemIndex == 0 or ":NOT" in target or ":NOT" in vocabElem:
                                continue
                            if target + ',' + vocabElem in overallPredicates:
                                predicatesHere.append(target + ',' + vocabElem)
                            elif vocabElem + "," + target in overallPredicates:
                             predicatesHere.append(vocabElem + "," + target)
                            
                        # if stateNameHere == "Wemo SmartPlug:Turn off":
                            # print(vocabList[int(historyCalc[-1])])
                            
                            
                        # if target == stateNameHere:
                            # target = "self"
                        # if not vocabList[int(historyCalc[0])].split(',')[0] == stateNameHere:
                            # continue
                      else:
                          target = vocabList[int(historyCalc[-1])].split(',')[0]
                          if vocabList[int(historyCalc[-1])] in predicateList[stateNameHere]["predicates"]:
                            predicatesHere = predicateList[stateNameHere]["predicates"][vocabList[int(historyCalc[-1])]].copy()
                          else:
                            predicatesHere = []
                          if not target in predicatesHere:
                            predicatesHere.append(target)
                          for vocabElemIndex, vocabElem in enumerate(vocabList[int(historyCalc[-1])].split(',')):
                            if vocabElemIndex == 0 or ":NOT" in target or ":NOT" in vocabElem:
                                continue
                            if target + ',' + vocabElem in overallPredicates:
                                predicatesHere.append(target + ',' + vocabElem)
                            elif vocabElem + "," + target in overallPredicates:
                             predicatesHere.append(vocabElem + "," + target)
                           
                          if vocabList[int(historyCalc[-2])].split(',')[0] == vocabList[int(historyCalc[-1])].split(',')[0] or target != stateNameHere:# or vocabList[int(historyCalc[-1])].split(',')[0] != stateNameHere:
                           target = "self"
                           #continue
                      # if stateNameHere == "Wemo SmartPlug:Turn off":
                        
                        # #print(vocabList[int(historyCalc[-2])].split(',')[0])
                        # #print(vocabList[int(historyCalc[-1])].split(',')[0])
                        
                        
                      
                      
                      try:
                        cp, ngram, bw = line.strip().split('\t')
                        ngram_bw_store[ngram] = float(bw)
                      except ValueError:
                        cp, ngram = line.strip().split('\t')
                      if ngram.count(' '):
                        prefix, suffix = ngram.rsplit(' ', 1)
                        suffix = target
                        ngram_cp_store[prefix].append((suffix, float(cp)))
                        if not prefix in ngram_cp_storePredicates:
                            ngram_cp_storePredicates[prefix] = {}
                        for predicateHere in predicatesHere:  
                            if ":NOT" in predicateHere:
                                continue
                            if not predicateHere in ngram_cp_storePredicates[prefix]:
                                ngram_cp_storePredicates[prefix][predicateHere] = 0
                            ngram_cp_storePredicates[prefix][predicateHere] += 10**float(cp)
                      else:
                      
                        for predicateHere in predicatesHere:
                            if ":NOT" in predicateHere:
                                continue
                            if not predicateHere in ngram_cp_storePredicates["Base"]:
                                ngram_cp_storePredicates["Base"][predicateHere] = 0
                            ngram_cp_storePredicates["Base"][predicateHere] += 10**float(cp)
                        if not target in ngram_cp_store:
                            ngram_cp_store[target] = float(0)
                        ngram_cp_store[target] += 10**float(cp)
                        bucketDivide += 10**float(cp)
                    if bucketDivide > 0:
                        for elemHere in ngram_cp_store:
                            if isinstance(ngram_cp_store[elemHere],list): 
                                continue
                            ngram_cp_store[elemHere] = ngram_cp_store[elemHere]/bucketDivide
                    ngram_bucketsSelf.append(ngram_cp_store)
            stateNumTracker += len(vocabList)
            vocab_file = "tempVocabFile.vocab"
            order =  3
            training_file = "tempTrainingFileNoSelfs.train"
            op = ['-v', vocab_file, '-o', str(order), '-s', "ModKN"]
            mitlmi = ['estimate-ngram', '-t', training_file, '-wl', 'ilmContext','-verbose','0']
            mitlmi.extend(op)
            
            try:
                subprocess.check_output(mitlmi)
            except (subprocess.CalledProcessError, FileNotFoundError) as e:
                print(stateNameHere)
                print(vocabList)
                #print(currentLine)
                print("2")
                print()
                #sys.stderr.write(repr(e) + "\n2\n")
                validGraph = 0
                #sys.exit(1) 
            if validGraph == 1:
             with open("ilmContext", 'r') as f: 
                  arpa_model_header = []
                  ngram_buckets = []
                  ngram_bw_store = {}
                  distribution = {}
                  bucketDivide = 0
                  next(f) # skip 1st line
                  next(f) # skip 2nd line

                  for line in f:
                    if not line.strip():
                      break
                    arpa_model_header.append(int(line.strip().split('=')[-1]))

                  for bucket in range(len(arpa_model_header)):
                    next(f) # skip r'\\\d+-grams:'
                    ngram_cp_store = defaultdict(list) if bucket else {}
                    for line in f:
                      if not line.strip():
                        break
                      historyCalc = line.strip().replace('<','').replace('>','').split('\t')[1].split(' ')
                      target = 0
                      if 's' in historyCalc or '/s' in historyCalc:
                        continue
                      #Commented out, removed self-transitions
                      if len(historyCalc) == 1:
                        if line.count('<') > 1:
                            historyCalc = line.strip().split('>')[0].replace('<','').replace('>','').split('\t')[1].split(' ')
                        target = vocabList[int(historyCalc[-1])].split(',')[0]
                        if vocabList[int(historyCalc[-1])] in predicateList[stateNameHere]["predicates"]:
                            predicatesHere = predicateList[stateNameHere]["predicates"][vocabList[int(historyCalc[-1])]].copy()
                        else:
                            predicatesHere = []
                        if not target in predicatesHere:
                            predicatesHere.append(target)
                        for vocabElemIndex, vocabElem in enumerate(vocabList[int(historyCalc[-1])].split(',')):
                            if vocabElemIndex == 0 or ":NOT" in target or ":NOT" in vocabElem:
                                continue
                            if target + ',' + vocabElem in overallPredicates:
                                predicatesHere.append(target + ',' + vocabElem)
                            elif vocabElem + "," + target in overallPredicates:
                             predicatesHere.append(vocabElem + "," + target)
                        # if deviceIndex == 11 and stateNameHere == "Location:You enter an area":
                            # print(vocabList[int(historyCalc[-1])])
                            
                            
 
                        if target != stateNameHere:
                            target = "self"
                        # if not vocabList[int(historyCalc[0])].split(',')[0] == stateNameHere:
                            # continue
                      else:
                          target = vocabList[int(historyCalc[-1])].split(',')[0]
                          if vocabList[int(historyCalc[-1])] in predicateList[stateNameHere]["predicates"]:
                            predicatesHere = predicateList[stateNameHere]["predicates"][vocabList[int(historyCalc[-1])]].copy()
                          else:
                            predicatesHere = []
                          if not target in predicatesHere:
                            predicatesHere.append(target)
                          for vocabElemIndex, vocabElem in enumerate(vocabList[int(historyCalc[-1])].split(',')):
                            if vocabElemIndex == 0 or ":NOT" in target or ":NOT" in vocabElem:
                                continue
                            if target + ',' + vocabElem in overallPredicates:
                                predicatesHere.append(target + ',' + vocabElem)
                            elif vocabElem + "," + target in overallPredicates:
                             predicatesHere.append(vocabElem + "," + target)
                          if vocabList[int(historyCalc[-2])].split(',')[0] == vocabList[int(historyCalc[-1])].split(',')[0] or target != stateNameHere:# or vocabList[int(historyCalc[-1])].split(',')[0] != stateNameHere:
                           target = "self"
                           #continue
                          # if deviceIndex == 11 and stateNameHere == "Location:You enter an area":
                            # print(vocabList[int(historyCalc[-1])])
                            # print(vocabList[int(historyCalc[-2])].split(',')[0])
                            # print(vocabList[int(historyCalc[-1])].split(',')[0])
                            
                            
                      try:
                        cp, ngram, bw = line.strip().split('\t')
                        ngram_bw_store[ngram] = float(bw)
                      except ValueError:
                        cp, ngram = line.strip().split('\t')
                      if ngram.count(' '):
                        prefix, suffix = ngram.rsplit(' ', 1)
                        suffix = target
                        ngram_cp_store[prefix].append((suffix, float(cp)))
                        if not prefix in ngram_cp_storePredicates:
                            ngram_cp_storePredicates[prefix] = {}
                        for predicateHere in predicatesHere:
                            if ":NOT" in predicateHere:
                                continue
                            if not predicateHere in ngram_cp_storePredicates[prefix]:
                                ngram_cp_storePredicates[prefix][predicateHere] = 0
                            ngram_cp_storePredicates[prefix][predicateHere] += 10**float(cp)
                      else:
                         if not target in ngram_cp_store:
                            ngram_cp_store[target] = float(0)
                         ngram_cp_store[target] += 10**float(cp)
                         
                         bucketDivide += 10**float(cp)
                         for predicateHere in predicatesHere:
                            if ":NOT" in predicateHere:
                                continue
                            if not predicateHere in ngram_cp_storePredicates["Base"]:
                                ngram_cp_storePredicates["Base"][predicateHere] = 0
                            ngram_cp_storePredicates["Base"][predicateHere] += 10**float(cp)
                    if bucketDivide > 0:
                        for elemHere in ngram_cp_store:
                            if isinstance(ngram_cp_store[elemHere],list): 
                                continue
                            ngram_cp_store[elemHere] = ngram_cp_store[elemHere]/bucketDivide
                    ngram_buckets.append(ngram_cp_store)
            else:
                ngram_buckets = []
            #if deviceIndex % 5 == 0 and deviceIndex != 0:
             #   print(deviceIndex)
              #  print(stateNumTracker)
               
            # if deviceIndex == 11 and stateNameHere == "Location:You enter an area":
                        # exit()
            # print(deviceIndex)
            
            # print(stateNameHere)
            # print(chiSquareResults[stateNameHere])
            # print()
            modelDict[str(deviceIndex) + '-' + stateNameHere] = [ngram_buckets.copy(),chiSquareResults[stateNameHere].copy(),singleVocabList.copy(),vocabList.copy(),[],simpleList[deviceIndex][1],simpleList[deviceIndex][2], ngram_cp_storePredicates.copy()]
        # for relevantDevice in chiSquareResults:
            
            
            
            # # if not relevantDevice in modelDict:
                # # modelDict[relevantDevice] = []
            # #modelDict[relevantDevice].append([ngram_buckets.copy(),simpleList[deviceIndex].copy(),device,vocabList.copy(),[],simpleList[deviceIndex][1]])
            # modelDict[relevantDevice] = [ngram_buckets.copy(),chiSquareResults[relevantDevice].copy(),device,vocabList.copy(),[],simpleList[deviceIndex][1]]
            #distribution = deepcopy(ngram_buckets[0])
    # for modelPart in modelDict:
        
        
    # with open("StateSpaceSize.txt",'a') as stateFile:
        # stateFile.write(str(stateNumTracker) + '\n')
 
    unseenStates = []
    unseenTransitions = {}
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/predictionDict2.txt", "wb") as myFile:
            pickle.dump(modelDict, myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/overallPredicates.txt", "wb") as myFile:
            pickle.dump(overallPredicates, myFile)
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/predicateList.txt", "wb") as myFile:
            pickle.dump(predicateList, myFile)
            
    
    evalFirstLine = 0
    measureTime = 0
    statesInTraining = []
    with open("trainingFileContext.train", 'w') as trainingFile:
        with open("transitionMap.csv", 'w') as transitionFile:
        #with open("trainingFileContext.train", 'w') as trainingFile:
            with open("trainingFileTime.train", 'w') as trainingFileWaitTime:
            #with open("trainingFileTime.train", 'w') as trainingFileWaitTime:
                with open("/home/man5336/Documents/ProvPredictor/EvalFolder/evalFile.csv", 'w') as evalFile:
                #with open("evalFile.csv", 'w') as evalFile:
                    currentLine = ""
                    currentLineWait = ""
                    addedTransitions = 0
                    addedTransitionsWait = 0
                    startingHour = -1
                    startingMinute = -1
                    oldState = ""
                    largestIndex = 0
                    currentLine = ""
                    currentLineWait = ""
                    limitedOccuredStates = ""
                    oldState = ""
                    for stateIndex, stateToWrite in enumerate(stateHistorySimple):
                        
                        
                        if oldState != "" and (oldState + "=" + str(stateToWrite[1])) not in transitionMap:
                            transitionMap[(oldState + "=" + str(stateToWrite[1]))] = 1
                            transitionFile.write((oldState + "=" + str(stateToWrite[1])) + " ")
                        
                        if stateIndex == 0:
                            startingHour = int(str(stateToWrite[-1].hour))
                            startingMinute = int(str(stateToWrite[-1].minute))
                        if len(stateHistorySimple) - stateIndex == evaluationSize:
                            startingHour = int(str(stateToWrite[-1].hour))
                            startingMinute = int(str(stateToWrite[-1].minute))
                        if len(stateHistorySimple) - stateIndex == evaluationSize:
                            measureTime = stateToWrite[0] - timeStepLength
                        #A bad way to do states that occur concurrently
                        if stateIndex + 1 != len(stateHistorySimple) and stateHistorySimple[stateIndex + 1][0] == stateToWrite[0]:
                            continue
                        walkBack = 0
                        limitedOccurances = ""
                        while stateIndex - walkBack >= 0 and stateHistorySimple[stateIndex - walkBack][0] == stateToWrite[0] and stateHistorySimple[stateIndex - walkBack][2] != "":
                            limitedOccurances += stateHistorySimple[stateIndex - walkBack][2] + "_"
                            walkBack += 1
                        firstInstance = 1
                        writeHour = 1
                        #if stateIndex < simpleTrainingSpace:
                        
                        #if (splitStart == -1 and measureTime < simpleTrainingSpace) or (splitStart != -1 and measureTime < splitStart):
                        if (splitStart == -1 and stateIndex < simpleTrainingSpace) or (splitStart != -1 and measureTime < splitStart):
                            largestIndex = measureTime
                            if stateToWrite[1].split('-')[1] in unsafeToNotUse:
                                currentLine = currentLine + '\n'
                                continue
                            if oldState != "":
                                if not oldState in transitionsOccured:
                                    transitionsOccured[oldState] = []
                                if not stateToWrite[1].split('-')[1] in transitionsOccured[oldState]:
                                    transitionsOccured[oldState].append(stateToWrite[1].split('-')[1])
                            if not stateToWrite[1].split('-')[1] in statesInTraining:
                                statesInTraining.append(stateToWrite[1].split('-')[1])
                            if writeHour == 1:
                                writeHour = 0
                            while measureTime <= stateToWrite[0]:
                                currentLine = currentLine + "<" + str(stateToWrite[1]).split('-')[1] + "> "
                                if trackTime == 1:
                                        currentLineWait = currentLineWait + "<" + str(stateToWrite[1]).split('-')[0] + "-" +  str(startingHour) + "> "
                                else:
                                    currentLineWait = currentLineWait + "<" + str(stateToWrite[1]) + "> "
                                measureTime += timeStepLength
                                startingMinute += timeStepLength
                                if startingMinute >= 60:
                                    startingMinute = 0
                                    startingHour += 1
                                    if startingHour == 24:
                                            startingHour = 0
                                            writeHour = 1
                            if splitStart != -1 and not measureTime < splitStart:
                                currentLineWait = currentLineWait + '\n'
                        elif splitStart != -1 and  measureTime > splitEnd:
                            if stateToWrite[1].split('-')[1] in unsafeToNotUse:
                                currentLine = currentLine + '\n'
                                continue
                            largestIndex = measureTime
                            if oldState != "":
                                if not oldState in transitionsOccured:
                                    transitionsOccured[oldState] = []
                                if not stateToWrite[1].split('-')[1] in transitionsOccured[oldState]:
                                    transitionsOccured[oldState].append(stateToWrite[1].split('-')[1])
                            if  stateToWrite[1].split('-')[1] in unseenStates:
                                del unseenStates[unseenStates.index(stateToWrite[1].split('-')[1])]
                                statesInTraining.append(stateToWrite[1].split('-')[1])
                            if writeHour == 1:
                                writeHour = 0
                            while measureTime <= stateToWrite[0]:
                                currentLine = currentLine + "<" + str(stateToWrite[1]).split('-')[1] + "> "
                                if trackTime == 1:
                                        currentLineWait = currentLineWait + "<" + str(stateToWrite[1]).split('-')[0] + "-" +  str(startingHour) + "> "
                                else:
                                    currentLineWait = currentLineWait + "<" + str(stateToWrite[1]) + "> "
                                measureTime += timeStepLength
                                startingMinute += timeStepLength
                                if startingMinute >= 60:
                                    startingMinute = 0
                                    startingHour += 1
                                    if startingHour == 24:
                                            startingHour = 0
                                            writeHour = 1
                        elif (splitStart == -1 and len(stateHistorySimple) - stateIndex <= evaluationSize) or (measureTime >= splitStart and measureTime <= splitEnd):   
                            if not stateToWrite[1].split('-')[1] in statesInTraining and not stateToWrite[1].split('-')[1] in unseenStates:
                                unseenStates.append(stateToWrite[1].split('-')[1])
                            if evalFirstLine == 0:
                                evalFirstLine = 1
                                oldState != ""
                                firstLineWritten = 0
                                for statePartHereIndex, statePartHere in enumerate(state):

                                    for statePartCurrentEvent in stateExtractionsContext[int(stateToWrite[1].split('-')[1])].split(','):
                                        if statePartHere == statePartCurrentEvent.split(':')[0]:
                                            if firstLineWritten != 0:
                                                evalFile.write(',')
                                            else:
                                                firstLineWritten = 1
                                            evalFile.write(str(statePartHereIndex) + '-' + statePartCurrentEvent)
                                evalFile.write('~')
                                for statePartHereIndex, statePartHere in enumerate(stateExtractionsContext[int(stateToWrite[1].split('-')[1])].split(',')):
                                    if statePartHereIndex != 0:
                                        evalFile.write(',')
                                    evalFile.write(statePartHere)
                                
                                evalFile.write('\n')
                            eventString = ""
                            if oldState != "":
                                if not oldState in transitionsOccured or not stateToWrite[1].split('-')[1] in transitionsOccured[oldState]:
                                    if not stateToWrite[1].split('-')[1]  in unseenTransitions:
                                        unseenTransitions[stateToWrite[1].split('-')[1] ] = []
                                    if not oldState in unseenTransitions[stateToWrite[1].split('-')[1] ]:
                                        unseenTransitions[stateToWrite[1].split('-')[1]].append(oldState)
                                
                            for trigger in structuredEvents[stateIndex]["Triggers"]:
                                eventString += str(deviceNames.index(structuredEvents[stateIndex]["Triggers"][trigger]["Service"])) + '-' + structuredEvents[stateIndex]["Triggers"][trigger]["Service"] + ":" + trigger
                            for action in structuredEvents[stateIndex]["Actions"]:
                                eventString += "," +  str(deviceNames.index(structuredEvents[stateIndex]["Actions"][action]["Service"])) + '-' + structuredEvents[stateIndex]["Actions"][action]["Service"] + ":" + action
                            while measureTime < stateToWrite[0]:
                                
                                if trackTime == 1:
                                        evalFile.write(eventString + "~" + str(stateToWrite[1]) + "-" +  str(startingHour) + ":" + str(startingMinute)  + "\n")
                                else:
                                    evalFile.write(eventString + '\n')
                                if str(stateToWrite[1]) in simpleUnsafeStates:
                                    if str(stateToWrite[1])  in stateOccurances:
                                            stateOccurances[str(stateToWrite[1]) ] += 1
                                    else:
                                        stateOccurances[str(stateToWrite[1]) ] = 1
                                measureTime += timeStepLength
                                startingMinute += timeStepLength
                                if startingMinute >= 60:
                                    startingMinute = 0
                                    startingHour += 1
                                    if startingHour == 24:
                                        startingHour = 0
                        oldState = str(stateToWrite[1].split('-')[1])
                trainingFile.write(currentLine)
                #print(len(currentLineWait.split(' ')))
                trainingFileWaitTime.write(currentLineWait[:-1])
    
    
    # exit()


#Uncomment out below here
    # vocab_file = "vocabFileTime.vocab"
    # #vocab_file = "vocabFileTime.vocab"
    # order =  3
    # #training_file = "trainingFileTime.train"
    # training_file = "trainingFileTime.train"
    # op = ['-v', vocab_file, '-o', str(order), '-s', "ModKN"]

    # mitlmi = ['estimate-ngram', '-t', training_file, '-wl', "ilmTime"]
    # mitlmi.extend(op)
    # try:
        # subprocess.check_output(mitlmi)
    # except (subprocess.CalledProcessError, FileNotFoundError) as e:
        # sys.stderr.write(repr(e))
        # sys.exit(1)
    
    vocab_file = "vocabFileContext.vocab"
    #vocab_file = "vocabFileContext.vocab"
    order =  3
    #training_file = "trainingFileContext.train"
    training_file = "trainingFileContext.train"
    op = ['-v', vocab_file, '-o', str(order), '-s', "ModKN"]

    mitlmi = ['estimate-ngram', '-t', training_file, '-wl', '/home/man5336/Documents/ProvPredictor/EvalFolder/ilmContext','-verbose','0']
    mitlmi.extend(op)
    try:
        subprocess.check_output(mitlmi)
        #subprocess.run(mitlmi,stdout=subprocess.DEVNULL)
    except (subprocess.CalledProcessError, FileNotFoundError) as e:
        sys.stderr.write(repr(e))
        sys.exit(1)

    occuranceConfirmer = {}
    historyConfirmer = []
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/ilmContext", 'r') as ilmFile:    
        ilmList = list(ilmFile)
        for item in ilmList:
            if len(re.findall("<[0-9]*-[0-9]*>",item)) == 2:
                historyConfirmer.append(re.findall("<[0-9]*-[0-9]*>",item)[0] + ' ' + re.findall("<[0-9]*-[0-9]*>",item)[1])
                for state in re.findall("<[0-9]*-[0-9]*>",item):
                    if not state in occuranceConfirmer:
                        occuranceConfirmer[state] = 0
            elif len(re.findall("<[0-9]*-[0-9]*>",item)) == 1:
                historyConfirmer.append(re.findall("<[0-9]*-[0-9]*>",item)[0])

    currentHistory = []
    
    unseenHistories = []
    oldElem = ""

    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/evalFile.csv", 'r') as evalFile:   
        evalList = list(evalFile)
        
        for evalElemIndex, evalElem in enumerate(evalList):
            if evalElemIndex == 0:
                continue
            evalElem = evalElem.split('~')[1]
            evalElem = evalElem.split('-')[0] + '-' + evalElem.split('-')[1]
            if oldElem == "" or not oldElem == evalElem:
                if currentHistory == []:
                    currentHistory = [evalElem]
                    if not currentHistory[0] in historyConfirmer and not currentHistory[0] in historyConfirmer:
                        unseenHistories.append("<" + currentHistory[0] + ">") 
                else:
                    if len(currentHistory) == 1:
                        currentHistory.append(evalElem)
                    else:
                        del currentHistory[0]
                        currentHistory.append(evalElem)
                    historyString = "<" + currentHistory[0] + "> <" + currentHistory[1] + ">"
                    if not historyString in historyConfirmer and not historyString in unseenHistories:
                        unseenHistories.append(historyString) 
            oldElem = evalElem
        
    
    # print("Start here")
    
    
    
    # for unseenState  in unseenStates:
        # unseenSplit = stateExtractionsContext[int(unseenState)].split(',')
        # overallDifferences = []
        # for extractedIndex, extractedState in enumerate(stateExtractionsContext):
            # if str(extractedIndex) in unseenStates:
                # print("Continued")
                # continue
            # extractedSplit = extractedState.split(',')
            # differences = []
            # for splitIndex, unseenPart in enumerate(unseenSplit):
                # if unseenPart != extractedSplit[splitIndex] and not unseenPart in differences:
                    
                    
                    
                    # differences.append(unseenPart)
            # if len(differences) == 1:
                # overallDifferences.append(differences[0])
        
        
        
        # exit()
        
    # exit()
    unseenStates = [unseenToDo]
    unseenTransitions["Unseen"] = unseenStates
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/transitionsInTraining2.txt", "wb") as myFile:
            pickle.dump(unseenTransitions, myFile)
    replacements = []
    usedStates = []
    matches = 0
    noMatches = 0
    
    averageLikelihood = []
    replacers = []
    # with open("ilmContext", 'r') as ilmFile:    
        # ilmList = list(ilmFile)
        # for ilmLine in ilmList:
            
            # ilmSplit = ilmLine.split(',')
            # if len(ilmSplit) == 3:
                # averageLikelihood = 10**float(ilmSplit[-1])
                # if 10**float(ilmSplit[-1]) < .05:
                    # replacers.append([ilmSplit[-2],''])
    # deleteable = []
    # for replaced in replacers:
        # deleteable.append(overallStateExtractions.index(replaced[0]))
        # for stateExtractionCalc  in overallStateExtractions:
            # continue
    # print(statistics.mean(averageLikelihood))
    # exit()
    for history in unseenHistories:
        bestMatch = [history,-1,-1]
        statesDivided = history.split(" ")
        for existingHistory in historyConfirmer:
            historyDivided = existingHistory.split(" ")
            found = 1
            if len(statesDivided) != len(historyDivided):
              continue
            for stateIndex, stateCheck in enumerate(statesDivided):
                if not stateCheck.split("-")[0] == historyDivided[stateIndex].split("-")[0]:
                  found = 0
                  break
            differences = 0    
            if found == 1:
              if trackTime == 0:
                  for stateIndex, stateCheck in enumerate(statesDivided):
                    firstContext = stateExtractionsContext[int(stateCheck.split("-")[1].replace('>',''))].split(',')
                    secondContext = stateExtractionsContext[int(historyDivided[stateIndex].split("-")[1].replace('>',''))].split(',')
                    for contextIndex, contextElem in enumerate(firstContext):
                      if contextElem != secondContext[contextIndex]:
                        differences += 1
                  if bestMatch[1] == -1 or bestMatch[2] > differences:
                    bestMatch = [history,existingHistory,differences]
            else:
                  for stateIndex, stateCheck in enumerate(statesDivided):
                    firstContext = int(stateCheck.split("-")[1].replace('>',''))
                    secondContext = int(historyDivided[stateIndex].split("-")[1].replace('>',''))
                  
                    differences = abs(firstContext-secondContext)
                  if bestMatch[1] == -1 or bestMatch[2] > differences:
                    bestMatch = [history,existingHistory,differences]

        
        if bestMatch[1] == -1:
          
          noMatches += 1
        else:
          replacements.append(bestMatch.copy())
          
          matches += 1
        if bestMatch[1] != -1 and not bestMatch[1] in usedStates:
          usedStates.append(bestMatch[1])
    
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/evalFile.csv", 'r') as evalFile:   
        evalList = list(evalFile)
        # print(len(overallStateExtractions))
        # print(len(unseenHistories))
        # exit()
        # deleteable = []
        # for stateExtractionCalc in unseenHistories:
            # if stateExtractionCalc in overallStateExtractions:
                # deleteable.append(overallStateExtractions.index(stateExtractionCalc))
        # for evalElem in evalList: 
            # exit()
    fileToWrite = []
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/ilmContext", 'r') as ilmFile:    
        ilmList = list(ilmFile)
        for item in ilmList:
          fileToWrite.append(item)
          if len(re.findall("<[0-9]*-[0-9]*>",item)) == 2:
            historyString = re.findall("<[0-9]*-[0-9]*>",item)[0] + ' ' + re.findall("<[0-9]*-[0-9]*>",item)[1]
            if historyString in usedStates:
              lineElems = item.split(" ")
              
              probability = lineElems[0]
              for replacement in replacements:
                if replacement[1] == historyString:
                  fileToWrite.append(lineElems[0].split('\t')[0] + "\t" + replacement[0] + "\n")
                  
          elif len(re.findall("<[0-9]*-[0-9]*>",item)) == 1:
            historyString = re.findall("<[0-9]*-[0-9]*>",item)[0]
    with open("/home/man5336/Documents/ProvPredictor/EvalFolder/ilmContext", 'w') as ilmFile:    
    #with open("ilmContext", 'w') as ilmFile:    
      for part in fileToWrite:
        ilmFile.write(part)
    reduced = 0

exit()
for occurance in stateOccurances:
            print(occurance)
            print(stateOccurances[occurance])

exit()
for stateData in stateHistory[len(stateHistory)-1]:
    stateDataFull = stateHistory[len(stateHistory)-1][stateData]
    if stateData != "Time":
        fieldString = ""
        for field in stateDataFull["fields"]:
            fieldString = fieldString + field + ":" + stateDataFull["fields"][field] + "-"
        if fieldString != "":
            fieldString = fieldString[:-1]
        ingredientString = ""
        for ingredient in stateDataFull["ingredients"]:
            ingredientString = ingredientString + ingredient + ":" + stateDataFull["ingredients"][ingredient] + "-"
        if ingredientString != "":
            ingredientString = ingredientString[:-1]
        #print("%s/%s/%s/%s" % (stateData,stateDataFull["state"],fieldString,ingredientString))



oldState = ""
occuranceTracker = {}
for service in services:
    occuranceTracker[service] = {}
    
#Ignored states for reducing number of states for explosion
#ignoredStates = ["Every month on the","Set ringtone volume","Create a detailed event","Humidity falls below threshold","Humidity rises above threshold"]
for index, state in enumerate(stateHistory):
    simpleState = ""
    for elemIndex, elem in enumerate(state):
        if elemIndex != (len(state) - 1):
            simpleState = simpleState + state[elem]["state"]
            # if not state[elem]["state"] in ignoredStates:
                # simpleState = simpleState + state[elem]["state"]
            # else:
                # simpleState = simpleState + stateHistory[index-1][elem]["state"]
            if state[elem]["state"] in occuranceTracker[elem]:
                occuranceTracker[elem][state[elem]["state"]] += 1
            else:    
                occuranceTracker[elem][state[elem]["state"]] = 1
            
    
    if not (simpleState in stateIndexes):
        # if index > 0:
            # difference = ""

            # for elemIndex, elem in enumerate(state):
                # if elemIndex != (len(state) - 1):
                    # if state[elem]["state"] != oldState[elem]["state"]:
                        # difference = difference + state[elem]["state"]
            # #print("Diff: %s" % (difference))
        if len(stateIndexes) == 0 or len([li for li in difflib.ndiff(simpleState, stateIndexes[-1]) if li[0] != ' ']) != 0:
            stateIndexes.append(simpleState)
            oldState = state
    stateIDs.append(stateIndexes.index(simpleState))
print(stateIndexes)
exit()    
for unsafeState in unsafeStateList:
  simpleState = ""
  for elemIndex, elem in enumerate(unsafeState[1]):
      if elemIndex != (len(unsafeState[1]) - 1):
        simpleState = simpleState + unsafeState[1][elem]["state"]
    
  if not stateIDs[stateIndexes.index(simpleState)] in unsafeStateListLiteral:
    unsafeStateListLiteral.append(stateIDs[stateIndexes.index(simpleState)])
# for service in occuranceTracker:

    # for elem in occuranceTracker[service]:
        # if occuranceTracker[service][elem] < 10:
            # #print("Service:%s" % (service))
            # #print("Elem:%s occured  %d" % (elem,occuranceTracker[service][elem]))
            
print(unsafeStateListLiteral)
exit()

stateOccurances = [0 for i in range(len(stateIndexes))]
with open('realStatesFormatted.csv', 'w', newline='') as csvfile:
    stateWriter = csv.writer(csvfile, delimiter=',', quotechar='|', quoting=csv.QUOTE_MINIMAL)
    currentStateIndex = 0
    while currentTime < newestTime:
        if stateHistory[currentStateIndex]["Time"] <= currentTime:
            currentState = stateHistory[currentStateIndex]
            currentState["Time"] = currentTime
            currentStateIndex += 1
        stateOccurances[stateIDs[currentStateIndex]] += 1
        stateWriter.writerow([str(currentTime.hour) + ":" + str(currentTime.minute),stateIDs[currentStateIndex]])
        currentTime = currentTime + timeStep
    currentState = state
    currentTime = currentTime + timeStep
    currentState["Time"] = currentTime
    stateWriter.writerow([str(currentTime.hour) + ":" + str(currentTime.minute),stateIDs[currentStateIndex]])
for index, occurance in enumerate(stateOccurances):
  if occurance > 500:
    print("%d:%d" % (index,occurance))


for service in services: 
    #continue
    if service == "Magic Hue"  or service == "AirThings" or service == "Android SMS" or service == "Location" or service == "Finance"  or service == "Make it Donate" or service == "Wemo SmartPlug":
        #print("Service:%s" % service)
        #print(services[service].stateExtractions)
        for trigger in services[service].elements[0]:
            numberOfPossibleStates += 1
            #print("Trigger:%s" % trigger)
            #print(services[service].elements[0][trigger].occurances)
            # for field in services[service].elements[0][trigger].fields:
                # #print("Field:%s\nValues:%s" % (field,services[service].elements[0][trigger].fields[field]))
            # for ingredient in services[service].elements[0][trigger].ingredients:
                # #print("Ingredient:%s\nValues:%s" % (ingredient,services[service].elements[0][trigger].ingredients[ingredient]))
            
        for query in services[service].elements[1]:
            numberOfPossibleStates += 1
            #print("Query:%s" % query)
            #print(services[service].elements[1][query].occurances)
            # for field in services[service].elements[1][query].fields:
                # #print("Field:%s\nValues:%s" % (field,services[service].elements[1][query].fields[field]))
            # for ingredient in services[service].elements[1][query].ingredients:
                # #print("Ingredient:%s\nValues:%s" % (ingredient,services[service].elements[1][query].ingredients[ingredient]))
            
        for action in services[service].elements[2]:
            numberOfPossibleStates += 1
            #print("Action:%s" % action)
            #print(services[service].elements[2][action].occurances)
            # for field in services[service].elements[2][action].fields:
                # #print("Field:%s\nValues:%s" % (field,services[service].elements[2][action].fields[field]))
            
        #print("-------------------------------------------------------------------------")
        #print("")
eventProbabilityList = []
for eventIndex, event in enumerate(structuredEvents):
    newEvent = [[],[],"",[],1]
    found = -1
    for index, trackedEvent in enumerate(eventProbabilityList):
        found = -1
        newEvent = [[],[],[],[],1]
        for checkIndex, element in enumerate(event["Triggers"]):
            newEvent[0].append([element,event["Triggers"][element]["Fields"]])
            if not (len(trackedEvent[0]) > checkIndex and element == trackedEvent[0][checkIndex][0]):
                found = 0
                break
            for field in event["Triggers"][element]["Fields"]:
                if not (field in trackedEvent[0][checkIndex][1] and event["Triggers"][element]["Fields"][field] == trackedEvent[0][checkIndex][1][field]):
                    found = 0
                    break

        for checkIndex, element in enumerate(event["Queries"]):
            newEvent[1].append([element,event["Queries"][element]["Fields"]])
            if not (len(trackedEvent[1]) > checkIndex and element == trackedEvent[1][checkIndex][0]):
                found = 0
                break
            for field in event["Queries"][element]["Fields"]:
                if not (field in trackedEvent[1][checkIndex][1] and event["Queries"][element]["Fields"][field] == trackedEvent[1][checkIndex][1][field]):
                    found = 0
                    break

        for checkIndex, element in enumerate(event["Actions"]):
            newEvent[3].append([element,event["Actions"][element]["Fields"]])
            
            if not (len(trackedEvent[3]) > checkIndex and element == trackedEvent[3][checkIndex][0]):
                found = 0
                break
            # for field in event["Actions"][element]["Fields"]:

                # if not (field in trackedEvent[3][checkIndex][1] and event["Actions"][element]["Fields"][field] == trackedEvent[3][checkIndex][1][field]):
                    # found = 0
                    # break

        if found == -1:
            found = index
            break
    if len(eventProbabilityList) == 0:
        eventProbabilityList.append(newEvent)
    elif found == 0:
        eventProbabilityList.append(newEvent)
    else:
        eventProbabilityList[found][4] = eventProbabilityList[found][4] + 1
# #print(len(structuredEvents))
# for event in eventProbabilityList:
    


exit()
print(numberOfPossibleStates)   
print(numberOfPossibleStates * 144)    
numberOfPossibleStates = 2**numberOfPossibleStates
print(numberOfPossibleStates)   
exit()
transitionMatrix = [1/numberOfPossibleStates] * numberOfPossibleStates    

print(numberOfPossibleStates)



    
    
    
    
    
        
            
