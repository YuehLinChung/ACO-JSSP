import sys                              #for maxFloat
import random
from collections import defaultdict
import datetime
import copy                             #for saving best objects
from time import time
import numpy as np
import pandas as pd
import itertools, json, pymysql
############################## INITIALIZATION --- START
timeline = defaultdict(list)
with open('META.json') as json_file:
    META = json.load(json_file)
    del json_file
MACHINETYPE_CLOTHNO = {'龍頭':['WS-1234'],'桃盤':['WS-5234','WS-6234']}
META['MachineTypeClothNo'] = MACHINETYPE_CLOTHNO
# with open('META.json','w') as json_file:
#     json.dump(META, json_file, indent=4)
# numMachines = len(META['MachineList'])
def initialization():
    random.seed(0)
    global totalStartTime
    totalStartTime = '2020-09-01 00:00:00'
    totalStartTime = datetime.datetime.strptime(totalStartTime, '%Y-%m-%d %H:%M:%S')
    global numJobs, numMachines, numNodes
    numMachines = 26
    parameterInitialization(50, 50) #input number of ants and cycles //Needed before creating node object

    #machine numbers are indexed starting at 1
    # Job1MachSeq = [1,2,3]
    # Job2MachSeq = [2,1,3]
    # Job3MachSeq = [1,3,2]

    global config
    config = ScheduleConfig()
    config.addJob([],5,0, orderNo='MO-10906022-0', clothNo='WS-1234')
    config.addJob([],6,1,deadline=11, orderNo='MO-10906023-0', clothNo='WS-5234')
    config.addJob([],3,2, clothNo='WS-1234')
    config.addJob([],4,1,deadline=50, clothNo='WS-5234')
    config.addJob([],5,0, clothNo='WS-1234')#5
    config.addJob([],6,2,deadline=20, clothNo='WS-3234')
    config.addJob([],7,0,deadline=20, clothNo='WS-1234')
    config.addJob([],8,2,deadline=30, clothNo='WS-5234')
    config.addJob([],9,3,deadline=20, clothNo='WS-3234')
    config.addJob([],10,0,deadline=24, clothNo='WS-5234')#10
    config.addJob([],11,1, clothNo='WS-3234')
    config.addJob([],12,2, clothNo='WS-3234')
    config.addJob([],5,2, clothNo='WS-1234')
    config.addJob([],7,1, clothNo='WS-5234')
    config.addJob([],8,2,deadline=25, clothNo='WS-1234')#15
    config.addJob([],4,1, deadline=4, clothNo='WS-3234')
    config.addJob([],7,3,deadline=30, clothNo='WS-3234')#17
    config.addJob([],9,1,start=35, clothNo='WS-3234')
    config.addJob([],10,3,deadline=11, clothNo='WS-5234')
    config.addJob([],20,4,deadline=30, clothNo='WS-3234')
    config.addJob([],26,5,deadline=30, clothNo='WS-1234')
    config.finish()

    global lockedNodes
    lockedNodes = LockedNode()
    # lockedNodes.add(10, start=30, end=40)
    # lockedNodes.add(2, start=1, end=3)
    # lockedNodes.add(3, start=3, end=6)
    # lockedNodes.add(16, start=3, end=7)
    # lockedNodes.add(19, start=1, end=13)
    global blockedSchedule
    blockedSchedule = BlockedSchedule()
    blockedSchedule.add(4,0,5)
    blockedSchedule.add(1,14,16)
    blockedSchedule.add(0,5,6)

    global NODESLIST
    NODESLIST = config.jobList #[Source,Node0,Node1,Node2,Node3,Node4,Node5,Node6,Node7,Node8,Node9,Node10,Node11,Node12,Node13,Node14,Node15,Node16,Node17,Node18,Sink] #the NODESLIST should be appended appropriately in numerical order
    numNodes = len(NODESLIST)

    #final note: sequential order is necessary and required for proper functionality at this stage.

    global ANTLIST
    ANTLIST = []

    global has_cycle
    has_cycle = False

    global smallestSoFarMakespan, bestSoFarAnt, smallestSoFarAntNum, bestSoFarANTLIST, bestSoFarNODESLIST
    bestSoFarANTLIST = []
    bestSoFarNODESLIST = []

    constructConjunctiveGraph()

    global solutionGraphList
    solutionGraphList = [[] for i in range(K)]
    generateSolutionGraphs()

    global nextMachine
    nextMachine = -1

    global currentMachine
    currentMachine = -1

    global feasibleNodeLists
    feasibleNodeLists = [[] for i in range(K)]

    global T
    T = [[0.2 for i in range(numNodes)] for j in range(numNodes)] #start with a small constant?

    global H #Heuristic matrix --- will this be different for different types/"species" of ants?.. TBD ***********************************************!!!!!!!!!!!!!!!
    H = [[0.5 for i in range(numNodes)] for j in range(numNodes)] #****************** NEEDS TO BE FIXED TO WORK WITH HEURISTICS

    global machineList
    machineList = [[] for i in range(numMachines)]
#TODO: 改成dict(str:int)或是為每台機器編號
    global cliquesVisited
    cliquesVisited = [[] for i in range(K)]

    generateAnts()
    generateMachineLists()

############################## INITIALIZATION --- END


############################## CLASSES --- START

class Node:
    def __init__(self, dependents, duration, machine, nodeNum, start=0, end=0,
                 orderNo='', clothNo='', deadline=100):
        self.duration = duration
        self.dependents = [copy.copy(dependents) for i in range(K)]
        self.init_deps = [n for n in dependents]#copy.deepcopy(dependents)
        self.machine = machine #可能是機器名稱(str)
        self.visited = False
        self.num = nodeNum
        self.startTime = 0
        self.endTime = 0
        self.scheduled = False
        self.antsVisited = [False for i in range(K)]
        self.name = 'name goes here' #fill in names via constructor
        self.discovered = False
        ### 擴充
        self.readyTime = start
        self.deadline = deadline
        self.orderNo = orderNo
        self.clothNo = clothNo
        self.yard = 0
        # self.machineNo = META['MachineList'].index(machine)
    def __repr__(self):
        return 'Node(num:%d duration:%d machine:%d start:%d end:%d)'%(self.num, self.duration, self.machine, self.startTime, self.endTime)

class Ant:
    def __init__(self, num):
        self.num = num #label each ant by a number 0 to (k-1)
        self.tabu = []
        self.position = -1
        self.T = [[0 for i in range(numNodes)] for j in range(numNodes)] #pheromone matrix
        self.pheromoneAccumulator = [[0 for i in range(numNodes)] for j in range(numNodes)] #accumulator
        self.transitionRuleMatrix = [[0 for i in range(numNodes)] for j in range(numNodes)] #for equation 1 transition probability
        self.makespan = 0
        self.species = 'none'
        self.cycleDetected = False
    def __repr__(self):
        return 'Ant: {}'.format(self.num)

class LockedNode:
    def __init__(self):
        self.nodes = []
        self.node_detail = {}

    def add(self, num, start, end, machine=None):
        """
        新增要鎖住的工作
        已存在則會覆蓋

        Args:
            num (int): 工作的編號，之後應改成用製令編號。\n
            start (int): 開始時間
            end (int): 結束時間
            machine (int, optional): 指定機器 Defaults to None.

        Returns:
            None.

        """
        if num not in self.nodes:
            self.nodes.append(num)
        if machine:
            self.node_detail[num] = (start, end, machine)
        else:
            self.node_detail[num] = (start, end)
class BlockedSchedule:
    def __init__(self):
        self.block=[]

    def add(self, machine, start, end):
        self.block.append((machine, start, end))

    def get(self, machine):
        if machine==None:
            return self.block
        else:
            return [x for x in self.block if x[0]==machine]

class ScheduleConfig():
    def __init__(self):
        self.jobList = [] #取代Node
        self.numJobs = 0 #取代numNodes
        self.totalStartTime = ''
        self.addJob([], 0, -1)

    def addJob(self, dependents, duration, machine, orderNo='',clothNo='',
               start=0, deadline:int=50):
        self.jobList.append(Node(dependents, duration, machine, len(self.jobList),
                                 orderNo=orderNo, clothNo=clothNo, start=start, deadline=deadline))
        self.numJobs += 1

    def finish(self):
        sinkDept = []
        for node in self.jobList[1:]:
            sinkDept.append(node)
            if len(node.init_deps) > 0:
                for n in node.init_deps:
                    if sinkDept.count(n) > 0:
                        sinkDept.remove(n)
        self.addJob(sinkDept, 0, -1)

    def findOrder(self, orderNo):
        for node in self.jobList:
            if node.orderNo == orderNo:
                return node
        raise Exception('orderNo: \"%s\" not found'%orderNo)

class JsonString():
    def __init__(self):
        self.__content=''

    def write(self, s):
        self.__content += s

    def get(self):
        return self.__content

    def clear(self):
        self.__content=''
############################## CLASSES --- END

############################## OTHER --- START

def parameterInitialization(numAnts, numCycles):
    global K, C, alpha, beta, rho
    global Q
    global Q1, Q2
    alpha = 0.2 #influence of pheromone
    beta = 1 - alpha #influence of heuristic
    rho = 0.7 #evaporation constant
    K = numAnts #number of ants
    C = numCycles #number of cycles
    Q1 = float(20) #**Programming Note: this must be a float in order for TSum to calculuate as float in calculatePheromoneAccumulation()
    Q2 = float(5)
    #EAS Procedure determination (below) of number of ants and fixed number of cycles
    #K = int(numJobs/2)
    #C = 1000
    #Q = float(5)  # //note: there is no Q1 and Q2 -- these are original

def generateAnts():
    for i in range(K):
        ANTLIST.append(Ant(i))

def generateMachineLists():
    for j in range(numNodes):
        if NODESLIST[j].machine != -1:
            machineList[NODESLIST[j].machine].append(NODESLIST[j].num)
# =============================================================================
#     for i in range(numMachines):
#         for j in range(numNodes):
#             if NODESLIST[j].machine == i:
#                 machineList[i].append(NODESLIST[j].num)
# =============================================================================

def generateSolutionGraphs():
    for k in range(K):
        constructConjunctiveGraph()
        solutionGraphList[k] = conjunctiveGraph
    #solutionGraphList in shape: (K, numNodes, numNodes)
def constructConjunctiveGraph():
    """
    conjunctiveGraph[i][j]代表從Node.num==i走到Node.num==j需花費的時間，也代表此路可通
    """
    global conjunctiveGraph
    conjunctiveGraph = [[-1 for i in range(numNodes)] for j in range(numNodes)]
    for node in NODESLIST[1:-1]:
        if len(node.init_deps) > 0:
            for dept in node.init_deps:
                conjunctiveGraph[dept.num][node.num] = NODESLIST[node.num].duration
# =============================================================================
#     for node1 in NODESLIST[1:-1]:
#         for node2 in NODESLIST[1:-1]:
#             if node1.num != node2.num:
#                 conjunctiveGraph[node1.num][node2.num] = NODESLIST[node2.num].duration
# =============================================================================
# =============================================================================
#         for seq1 in job.jobSequence:
#             for seq2 in job.jobSequence:
#                 if seq1 != seq2 and seq1+1 == seq2:#一定得連號??
#                     conjunctiveGraph[seq1+1][seq2+1] = NODESLIST[seq2+1].duration
# =============================================================================
    for j in range(1, numNodes-1):#從Source到每個Job的第一個Task的時間
        if len(NODESLIST[j].init_deps) == 0:
            conjunctiveGraph[0][j] = NODESLIST[j].duration
    for j in range(1, numNodes-1):#從Job最後一個Task到Sink花費的時間為0
        conjunctiveGraph[j][numNodes-1] = 0
    for node in NODESLIST[1:-1]:
        if len(node.init_deps) > 0:
            for dept in node.init_deps:
                for dept2 in dept.init_deps:
                    if dept2 in findAllDependents(dept):
                        conjunctiveGraph[dept2.num][node.num] = -1
                        #deep check depenpency, need recursive

                conjunctiveGraph[node.num][dept.num] = -1
                conjunctiveGraph[dept.num][numNodes-1] = -1
            conjunctiveGraph[0][node.num] = -1

def findAllDependents(node):
    if len(node.init_deps) == 0:
        return []
    temp = []
    for dept in node.init_deps:
        temp.append(dept)
        temp.extend(findAllDependents(dept))
    return temp

def chooseClique(antNum):
    machinesWithJob = [i for i in range(numMachines) if len(machineList[i])!=0]
    randomClique = random.choice(machinesWithJob)
    # randomClique = random.randint(0,numMachines-1) #choose Clique by random - we then choose to travel on nodes based off of pheromone trails - this prevents local optimia to occur
    while randomClique in cliquesVisited[antNum] or len(machineList[randomClique])==0:
        # randomClique = random.randint(0,numMachines-1)
        randomClique = random.choice(machinesWithJob)
    cliquesVisited[antNum].append(randomClique)
    return randomClique

def randomAssignment():
    for i in range(K):
        randNode = random.randint(1,numNodes-2)
        ANTLIST[i].tabu.append(NODESLIST[randNode].num)
        ANTLIST[i].position = randNode
        NODESLIST[randNode].antsVisited[i] = True

def defineDecidabilityRule():                                   #UNUSED 04/15/2017 -- For Heuristics **
    for ant in ANTLIST:
        speciesType = random.randint(1,2)
        if speciesType == 1:
            ant.species = 'SPT' #Shortest Processing Time (SPT)
        elif speciesType == 2:
            ant.species = 'LPT' #Longest Processing Time (LPT)

def dump(filename):
    result = {}
    for node in bestSoFarNODESLIST:
        result[node.num] = (node.startTime, node.endTime, node.machine)
    import joblib
    joblib.dump(result, filename)

def load(filename):
    import joblib
    nodeList = joblib.load(filename)
    return nodeList
############################## OTHER --- END

############################## SCHEDULING --- START

def schedule(ant):
    for node_num in lockedNodes.nodes:
        bestSoFarNODESLIST[node_num].startTime = lockedNodes.node_detail[node_num][0]
        bestSoFarNODESLIST[node_num].endTime = lockedNodes.node_detail[node_num][1]
        if len(lockedNodes.node_detail[node_num]) > 2:
            bestSoFarNODESLIST[node_num].machine = lockedNodes.node_detail[node_num][2]
    # print(bestSoFarNODESLIST[-1].dependents[ant.num])
    scheduleNode(bestSoFarNODESLIST[numNodes-1],ant)
    #把Sink餵進

def scheduleNode(node,ant):
    """
    Recursive直到node.dependents為空
    從Job中第一個工作開始排
    """

    if node.num in lockedNodes.nodes:
        node.startTime = lockedNodes.node_detail[node.num][0]
        node.endTime = lockedNodes.node_detail[node.num][1]
        # bestSoFarNODESLIST[node.num].startTime = lockedNodes.node_detail[node.num][0]
        # bestSoFarNODESLIST[node.num].endTime = lockedNodes.node_detail[node.num][1]
        if len(lockedNodes.node_detail[node.num]) > 2:
            node.machine = lockedNodes.node_detail[node.num][2]
            # bestSoFarNODESLIST[node.num].machine = lockedNodes.node_detail[node.num][2]
    # node.scheduled = True
    for proceedingNode in node.dependents[ant.num]:
        if proceedingNode.scheduled == False:# and not proceedingNode.num in lockedNodes.nodes:
            scheduleNode(proceedingNode,ant)
        # else:
        #     print(node, proceedingNode)
    # print(node)
    positionNode(node,ant) #base case
    node.scheduled = True

def positionNode(node,ant):
    if node.num in lockedNodes.nodes:
        return
    global longestProceedingTime
    node.startTime = findEarliestStartTime(node, ant, node.machine)
    bestSoFarNODESLIST[node.num].startTime = node.startTime
# =============================================================================
#     if len(node.dependents[ant.num])>0:
#         node.startTime = (bestSoFarNODESLIST[node.num].dependents[ant.num][0].startTime + node.dependents[ant.num][0].duration)
#         bestSoFarNODESLIST[node.num].startTime = (bestSoFarNODESLIST[node.num].dependents[ant.num][0].startTime + node.dependents[ant.num][0].duration)
#         for proceedingNode in node.dependents[ant.num]:
#             longestProceedingTime = (proceedingNode.startTime + proceedingNode.duration)
#             if longestProceedingTime > node.startTime: #Or xxxx [i for i in bestSoFarNODESLIST if i.machine==node.machine]
#                 # node.startTime = longestProceedingTime
#                 node.startTime = findEarliestStartTime(node, ant)
#                 bestSoFarNODESLIST[node.num].startTime = node.startTime #longestProceedingTime
#     else: #node has no proceeding nodes and can be scheduled right away
#         node.startTime = findEarliestStartTime(node, ant) #0
#         bestSoFarNODESLIST[node.num].startTime = node.startTime #0
# =============================================================================
    node.endTime = node.startTime + node.duration
    bestSoFarNODESLIST[node.num].endTime = node.startTime + node.duration

def findEarliestStartTime(node: Node, ant: Ant, machine):
    """


    Args:
        node (Node): 要排入行程的工作(Node)
        ant (Ant): 蟻群排序中最優解的那隻Ant
        machine (str): 該Node要放置在哪個machine中

    Returns:
        int: 該machine中最早可排時間之index

    """

    nodeList = [n for n in bestSoFarNODESLIST if n.machine==machine and n.endTime != 0]
    nodeList = sorted(nodeList, key=lambda n:n.endTime)
    if len(nodeList)==0 and len(blockedSchedule.get(machine))==0:
        return max([n.endTime for n in node.init_deps], default=0)
    max_dep_endtime = max([n.endTime for n in node.init_deps], default=0)
    max_end_time = max(nodeList[-1].endTime,max_dep_endtime) if len(nodeList)>0 else max_dep_endtime
    bucket = [False]*(node.duration + max([n[2]+1 for n in blockedSchedule.get(machine)]+[max_end_time], default=0))
    for n in nodeList:
        for seg in range(n.startTime, n.endTime):
            bucket[seg] = True
    ####----necessary??
    for n in node.dependents[ant.num]:
        for seg in range(n.startTime, n.endTime):
            bucket[seg] = True
    ####---------------
    for block in blockedSchedule.get(machine):
        bucket[block[1]:block[2]+1] = [True] * (block[2]-block[1]+1)

    if len(node.init_deps) > 0:
        deps = node.init_deps
        lastAvailableTime = max([n.endTime for n in deps], default=0)
        bucket[:lastAvailableTime]=[True]*lastAvailableTime
    idx = 0
    for seg in range(len(bucket)-node.duration+1):
        if bucket[seg:seg+node.duration] == [False]*node.duration:
            idx = seg
            break
    return idx

def detectChain(deploy: list) -> bool:
    """
    判斷是否有連接

    Args:
        deploy (list): list of deploy spec(dict).

    Returns:
        bool: if there is any chain in machine

    """
    if len(deploy) < 2:
        return False
    machineList = set(i['machine'] for i in deploy)
    for machine in machineList:
        choices = list(filter(lambda x: x['machine']==machine, deploy))
        for idx1 in range(len(choices)):
            for idx2 in range(len(choices)):
                if idx1 != idx2 and choices[idx1]['end'] == choices[idx2]['start']:
                    return True
############################## SCHEDULING --- END


############################## END OF CYCLE --- START

def calculatePheromoneAccumulation(ant,b):
    if b == 0:
        for i in range(numNodes):
            for j in range(numNodes):
                if i != j and solutionGraphList[ant.num][i][j] > 0:
                    ant.pheromoneAccumulator[i][j] += Q1/ant.makespan # calculate w.r.t. equation 3 or 4 *** //Python Note: in python 2.7 one of the two integers
                                                                    # must be a float, we declared Q as a float() type in the parameterInitialization() method
    elif b == 1:
        for i in range(numNodes):
            for j in range(numNodes):
                if i != j and solutionGraphList[ant.num][i][j] > 0:
                    ant.pheromoneAccumulator[i][j] += Q2/ant.makespan

def updatePheromone(bestMakespan, bestAntNum):
    TSum = 0
    TOld = T
    for i in range(numNodes):
        for j in range(numNodes):
            for ant in ANTLIST:
                TSum += ant.pheromoneAccumulator[i][j]
                ant.pheromoneAccumulator[i][j] = 0
            T[i][j] = TSum + rho*TOld[i][j] #update T[i][j] pheromone matrix based on equation 2 ***          ***c<1 accounted for in construction() [main] method***
            #pheromoneAccumulator[i][j] = 0   <---- Necessary?
            TSum = 0
    for i in range(numNodes):   #update for best ant
        for j in range(numNodes):
            if solutionGraphList[bestAntNum][i][j] > 0:
                T[i][j] += float(float(bestMakespan - solutionGraphList[bestAntNum][i][j])/float(bestMakespan))

def resetAnts():
    nextMachine = -1
    for k in range(K):
        # for i in range(numMachines):
        #     cliquesVisited[k].pop()
        cliquesVisited[k].clear()
    constructConjunctiveGraph()
    generateSolutionGraphs()
    #**LEARNING REMARK: #cliquesVisited = [[] for i in range(K)] *** NOTE: In Python this does not reset the variable/ double array list
    for ant in ANTLIST:
        ant.tabu = []
        ant.position = 0
        ant.T = [[0 for i in range(numNodes)] for j in range(numNodes)] #pheromone matrix
        ant.pheromoneAccumulator = [[0 for i in range(numNodes)] for j in range(numNodes)] #accumulator
        ant.makespan = 0
        ant.cycleDetected = False
    currentMachine = -1

def resetNodes():
    for k in range(K):
        for node in NODESLIST:
            node.visited = False
            node.antsVisited[k] = False
    for k in range(K):
        for node in NODESLIST:
            node.dependents[k]=[n for n in node.init_deps]

############################## END OF CYCLE --- END

############################## EXPLORATION --- START

def nextOperation(ant, machNum, cycle):
    findFeasibleNodes(ant, machNum)
    calculateTransitionProbability(ant)
    makeDecision(ant)

def findFeasibleNodes(ant,currentMachine):
    global feasibleNodeLists
    feasibleNodeLists = [[] for i in range(K)]
    for node in NODESLIST:
        if node.antsVisited[ant.num] == False: #04/04/17: Removed not()
            if node.num in machineList[currentMachine]:
                feasibleNodeLists[ant.num].append(node)

def calculateTransitionProbability(ant):
    pheromone = sum((((T[ant.position][l.num])**(alpha)) * ((H[ant.position][l.num])**(beta))) for l in feasibleNodeLists[ant.num])
    for node in feasibleNodeLists[ant.num]:
        if node.num not in ant.tabu:
            ant.transitionRuleMatrix[ant.position][node.num] = (((T[ant.position][node.num])**(alpha)) * ((H[ant.position][node.num])**(beta)))/pheromone

def makeDecision(ant):
    probabilityList = []                        #assign ranges between [0,1] and pick a rand num in interval.
    for node in feasibleNodeLists[ant.num]:
        probabilityList.append([ant.transitionRuleMatrix[ant.position][node.num]*100,node.num])
    for i in range(len(probabilityList)-1):
        probabilityList[i+1][0] += probabilityList[i][0]
    randomSelection = random.randint(0,100)
    selectedNode = -1
    for i in range(len(probabilityList)-1):
        if (probabilityList[i][0] <= randomSelection) and (randomSelection <= probabilityList[i+1][0]):
            selectedNode = probabilityList[i+1][1]
            break
        elif randomSelection <= probabilityList[i][0]: #should this be a strict less than, "<" ?
            selectedNode = probabilityList[i][1]
            break
    if selectedNode == -1:
        selectedNode = probabilityList[0][1]
    ant.position = selectedNode

############################## EXPLORATON --- END

############################## CONSTRUCTION PHASE --- START

def constructionPhase(): #The Probabilistic Construction Phrase of solutions begins by K ants
    for c in range(C):
        defineDecidabilityRule()
        for node in NODESLIST: #reset nodes visited to false since this is a new cycle
            for ant in ANTLIST:
                node.antsVisited[ant.num] = False
        for ant in ANTLIST:
            skip_counter = 0
            machinesWithJob = [i for i in range(numMachines) if len(machineList[i])!=0]
            for _ in range(len(machinesWithJob)):
                currentMachine = chooseClique(ant.num) #at random
                t = 0 #此Machine中，最快可以開始的時間
                if c<1:
                    # shuffledNodes = machineList[currentMachine]
                    random.shuffle(machineList[currentMachine]) #We could shuffle this list or we could just keep as is
                    for x in machineList[currentMachine]:
                        nowNode = config.jobList[x]
                        a = t - nowNode.readyTime #Node開始時間到Node原料齊貨日時間長
                        b = nowNode.deadline - t - nowNode.duration #Node結束時間距離deadline的時間長
                        if skip_counter%len(machineList[currentMachine]) != 0:
                            oldAntPosition = ant.position
                        ant.tabu.append(x)
                        ant.position = x
                        if skip_counter%len(machineList[currentMachine]) == 0:
                            NODESLIST[ant.position].antsVisited[ant.num] = True
                        if skip_counter%len(machineList[currentMachine]) != 0:
                            NODESLIST[ant.position].antsVisited[ant.num] = True
                            NODESLIST[ant.position].dependents[ant.num].append(NODESLIST[oldAntPosition])
                            # NODESLIST[-1].dependents[ant.num].remove(NODESLIST[oldAntPosition])
                            if a < 0:
                                solutionGraphList[ant.num][oldAntPosition][ant.position] = -50*a
                            if b < 0:
                                solutionGraphList[ant.num][oldAntPosition][ant.position] = -30*b
                                # solutionGraphList[ant.num][0][ant.position]*=0.9
                                # T[0][ant.position] *= 1.1
                                # for s in NODESLIST:
                                #     if solutionGraphList[ant.num][s.num][ant.position] > 0:
                                #         solutionGraphList[ant.num][s.num][ant.position] *= (0.99**(-b))
                            else:
                                solutionGraphList[ant.num][oldAntPosition][ant.position] = NODESLIST[ant.position].duration + (1/(b+1))
                                if NODESLIST[ant.position].clothNo == NODESLIST[oldAntPosition].clothNo and NODESLIST[ant.position].machine == NODESLIST[oldAntPosition].machine:
                                    solutionGraphList[ant.num][oldAntPosition][ant.position] -= 1
                        skip_counter += 1
                        t += nowNode.duration
                    skip_counter = 0
                else:
                    for _ in range(len(machineList[currentMachine])):
                        if skip_counter%len(machineList[currentMachine]) != 0:
                            moveFrom = ant.position
                        nextOperation(ant, currentMachine, c)
                        moveTo = ant.position
                        ant.tabu.append(moveTo)
                        nowNode = config.jobList[ant.position]
                        a = t - nowNode.readyTime
                        b = nowNode.deadline - t - nowNode.duration #Node距離deadline的時間
                        NODESLIST[moveTo].visited = True
                        NODESLIST[moveTo].antsVisited[ant.num] = True
                        if skip_counter%len(machineList[currentMachine]) != 0:#numJobs
                            NODESLIST[moveTo].dependents[ant.num].append(NODESLIST[moveFrom])
                            # NODESLIST[-1].dependents[ant.num].remove(NODESLIST[moveFrom])
                            if a < 0:
                                solutionGraphList[ant.num][moveFrom][moveTo] = -50*a
                                T[moveFrom][moveTo] /= (1.1**c)
                                # for i in range(numNodes):
                                #     T[i][moveTo] /= (1.01**c)
                                #     T[i][moveFrom] *= (1.02**c)
                            if b < 0:
                                solutionGraphList[ant.num][moveFrom][moveTo] = -30*b #NODESLIST[moveTo].duration*5
                                # solutionGraphList[ant.num][0][moveTo]*=0.9
                                for i in range(numNodes):
                                    T[i][moveTo] *= (1.02**c)
                                    T[i][moveFrom] /= (1.02**c)
                                # for s in NODESLIST:
                                #     if solutionGraphList[ant.num][s.num][moveTo] > 0:
                                #         solutionGraphList[ant.num][s.num][moveTo] *= (0.99**(c-b))
                                #     if solutionGraphList[ant.num][s.num][moveFrom] > 0:
                                #         solutionGraphList[ant.num][s.num][moveFrom] /= (0.95**(c-b))
                            else:
                                solutionGraphList[ant.num][moveFrom][moveTo] = NODESLIST[moveTo].duration + (1/(b+1)) # set equal to the duration of the moving to node (puts weight on edge)
                                if NODESLIST[moveTo].clothNo == NODESLIST[moveFrom].clothNo and NODESLIST[moveFrom].machine == NODESLIST[moveTo].machine:
                                    solutionGraphList[ant.num][moveFrom][moveTo] -= 1
                        skip_counter += 1
                        t += nowNode.duration
                    skip_counter = 0
        for ant in ANTLIST:
            undiscoverNodes()
            global has_cycle
            has_cycle = False
            cycleDetector(ant)
            ant.cycleDetected = has_cycle
            if ant.cycleDetected == False:
                ant.makespan = getMakespan(ant) #longest path in solution graph --- this is equivalent to the makespan
                calculatePheromoneAccumulation(ant,0)
            elif ant.cycleDetected == True:
                ant.makespan = sys.float_info.max
        smallestMakespan = sys.float_info.max
        smallestMakespan, smallestMakespanAntNum = getSmallestMakespan()
        calculatePheromoneAccumulation(ANTLIST[smallestMakespanAntNum],1) #reinforce the smallestMakespan ant
        if c > 0:
            global smallestSoFarMakespan, bestSoFarAnt
            if smallestMakespan < smallestSoFarMakespan:
                bestSoFarAnt = copy.deepcopy(ANTLIST[smallestMakespanAntNum])
                for i in range(numNodes):
                    bestSoFarNODESLIST[i] = copy.deepcopy(NODESLIST[i])
                for i in range(K):
                    bestSoFarANTLIST[i] = copy.deepcopy(ANTLIST[i])
                smallestSoFarMakespan = smallestMakespan
                smallestSoFarAntNum = smallestMakespanAntNum
        elif c == 0:
            bestSoFarAnt = copy.deepcopy(ANTLIST[smallestMakespanAntNum])
            for i in range(numNodes):
                bestSoFarNODESLIST.append(copy.deepcopy(NODESLIST[i]))
            for i in range(K):
                bestSoFarANTLIST.append(copy.deepcopy(ANTLIST[i]))
            smallestSoFarMakespan = smallestMakespan
            smallestSoFarAntNum = smallestMakespanAntNum
        updatePheromone(smallestMakespan, smallestMakespanAntNum)
        resetNodes()
        resetAnts()

    schedule(bestSoFarAnt)
    makeGanttChart(bestSoFarAnt)

############################## CONSTRUCTION PHASE --- END

############################## USED FOR DETECTING CYCLES --- START
def cycleDetector(ant):
    global has_cycle
    for node in NODESLIST:
        undiscoverNodes() #sets all nodes to undiscovered
        pcount = 0
        S = []  #let S be a stack
        S.append(node)
        while len(S) > 0:
            v = S.pop()
            if v.discovered == False:
                if v != node:
                    v.discovered = True
                if v == node and pcount >=1:
                    has_cycle = True
                    return
                for j in range(numNodes):
                    if solutionGraphList[ant.num][v.num][j] >= 0:
                        S.append(NODESLIST[j])
            pcount += 1

def undiscoverNodes():
    for node in NODESLIST:
        node.discovered = False

############################## USED FOR DETECTING CYCLES --- END


############################## MAKESPAN --- START

def getSmallestMakespan():
    smallestMakespan = sys.float_info.max #1.7976931348623157e+308
    smallestMakespanAntNum = -1
    for ant in ANTLIST:
        if ant.makespan < smallestMakespan:
            smallestMakespan = ant.makespan
            smallestMakespanAntNum = ant.num
    return smallestMakespan, smallestMakespanAntNum

def getMakespan(ant):
    G = defaultdict(list)
    edges = []
    for i in range(numNodes):
        for j in range(numNodes):
            if solutionGraphList[ant.num][i][j] != -1:
                edges.append([NODESLIST[i], NODESLIST[j]])
    for (s,t) in edges:
        G[s].append(t)
    all_paths = DFS(G,NODESLIST[0])
    max_len = 0
    max_paths = []
    max_makespan = 0
    path_duration = 0
    mkspnIndex_i = -1
    for i in range(len(all_paths)):
        path_duration = 0
        for j in range(len(all_paths[i])-1):
            path_duration += solutionGraphList[ant.num][all_paths[i][j].num][all_paths[i][j+1].num]#all_paths[i][j].duration
        if path_duration > max_makespan:
            max_makespan = path_duration
            mkspnIndex_i = i
    return max_makespan

def DFS(G,v,seen=None,path=None): #v is the starting node
    if seen is None: seen = []
    if path is None: path = [v]
    seen.append(v)
    paths = []
    for t in G[v]:
        if t not in seen:
            t_path = path + [t]
            paths.append(tuple(t_path))
            paths.extend(DFS(G, t, seen[:], t_path))
    return paths

############################## USED FOR GETTING MAKESPAN --- END

############################## GANTT --- START
def makeGanttChart(bestSoFarAnt):
    #quit()  #to not use more than 30 API calls per hour or 50 per day
    global df, colors
    import plotly.express as px
    df = []
    colors = []
    random.seed(2)
    for node in bestSoFarNODESLIST[1:-1]:
        s = str(totalStartTime + datetime.timedelta(days=node.startTime))
        d = str(totalStartTime + datetime.timedelta(days=node.endTime))
        r = str(totalStartTime + datetime.timedelta(days=node.readyTime))
        deadline = str(totalStartTime + datetime.timedelta(days=node.deadline))
        if node.endTime <= node.deadline:
            status = 'Meet'
        elif node.endTime > node.deadline:
            status = 'Not Meet'
        elif node.readyTime < node.startTime:
            status = 'Too Early'
        df.append(dict(Machine=str(node.machine), Start=str(s), Finish=str(d),
                      Task='{:02}'.format(node.num),
                      Duration=str('{} day(s)'.format(node.duration)),
                      Deadline=str(deadline),
                      Status=str(status),
                      ReadyTime=str(r),
                      ClothNo=node.clothNo))
        # colors.append('rgb(%d, %d, %d)'%(random.randint(0,255),random.randint(0,255),random.randint(0,255)))
    df.sort(key=lambda n:n['Task'])
    for block in blockedSchedule.block:
        s = str(totalStartTime + datetime.timedelta(days=block[1]))
        d = str(totalStartTime + datetime.timedelta(days=block[2]+1))

        df.append(dict(Machine=str(block[0]), Start=str(s), Finish=str(d),
                      Task='Lock',
                      Duration=str('{} day(s)'.format(block[2]-block[1]+1)),
                      Deadline=str(block[2]),
                      Status='Locked',
                      ReadyTime='Null',
                      ClothNo='Null'))
    # fig = ff.create_gantt(df, colors=colors, title='Schedule from 2017-04-18', index_col='Resource', show_colorbar=True, group_tasks=True)
    fig = px.timeline(df, x_start="Start", x_end="Finish", y="Machine", color="Status", hover_data=["Duration","ClothNo","ReadyTime","Deadline"], text="Task", title='Schedule from %s'%totalStartTime)
    fig.update_yaxes(autorange="reversed")
    with open('a_dense.html', 'w') as f:
        f.write(fig.to_html())
        f.close()

def getMachineList(cloth_no):
    conn = pymysql.connect('localhost', 'root', 'combo5210', 'wayson-dev-0901', connect_timeout=3)

    data = pd.read_sql_query("""SELECT weaving_machine_core_id
                                FROM cloth_core
                                	INNER JOIN cloth_tissue
                                	ON cloth_core.cloth_tissue_id = cloth_tissue.cloth_tissue_id
                                	INNER  JOIN weaving_machine_core
                                	ON cloth_tissue.fit_machine_type = weaving_machine_core.machine_type
                                WHERE cloth_core.cloth_no='%s'"""%cloth_no,conn)
    conn.close()
    machine_list = data.iloc[:,0].to_list()
    return machine_list

def findEarliestStartTimeFromDB(duration, machine:int, preload):
    conn = pymysql.connect('localhost', 'root', 'combo5210', 'wayson-dev-0901')
    data = pd.read_sql("""SELECT start_datetime, end_datetime
                       FROM weaving_machine_schedule
                       WHERE weaving_machine_core = {}
                       AND end_datetime > '{}'""".format(machine,totalStartTime.strftime('%Y-%m-%d %H:%M:%S')), conn)
    conn.close()
    if data.shape[0] == 0 and len(preload)==0:
        return totalStartTime.date()
    try:
        data['start_datetime'] = data['start_datetime'].dt.date
        data['end_datetime'] = data['end_datetime'].dt.date
        data['start_datetime'] = data['start_datetime'].apply(lambda x:max(x, totalStartTime.date()))
        dist = (data['start_datetime'].min() - totalStartTime.date()).days
        bucket = [False] * ((data['end_datetime'].max() - totalStartTime.date()).days + duration +1)
    except:
        bucket = [False] * ((datetime.datetime.strptime(max([n['end'] for n in preload]), '%Y-%m-%d').date()-totalStartTime.date()).days + duration + 1)
    
    for dep in preload:
        if int(dep['machine']) == machine:
            idx0 = (datetime.datetime.strptime(dep['start'], '%Y-%m-%d').date()-totalStartTime.date()).days
            idx1 = (datetime.datetime.strptime(dep['end'], '%Y-%m-%d').date()-totalStartTime.date()).days +1
            bucket[idx0:idx1] = [True]*(idx1-idx0)
    for it in data.itertuples():
        idx0 = (it.start_datetime-totalStartTime.date()).days
        idx1 = (it.end_datetime-totalStartTime.date()).days+1
        bucket[idx0:idx1] = [True]*(idx1-idx0)
    idx = 0
    for seg in range(len(bucket)-duration+1):
        if bucket[seg:seg+duration] == [False]*duration:
            idx = seg
            break
    return (totalStartTime.date() + datetime.timedelta(days=idx))

def getSolutions(numOfSegs, taskLength, deadline, clothNo):
    specNumSeg = numOfSegs + 1
    length = taskLength
    try:
        machine_list = getMachineList(clothNo)
    except:
        machine_list = []
    # deadline = 23
        # print([i for i in itertools.combinations_with_replacement(range(length+1),numSeg) if sum(i)==length])
    tmp_list = [i for i in itertools.combinations_with_replacement(range(length+1),specNumSeg) if sum(i)==length] #.append(tuple(sorted([len(n) for n in p.split('+')])))
    # tmp_set = set(tmp_list)
    solutions = {}

    for numSeg in range(1, specNumSeg+1):
        choices = []
        '''取numSeg段的選項'''
        for i in filter(lambda item: item.count(0)==specNumSeg - numSeg, tmp_list):
            choices.append(i[-numSeg:])
            # print(i[-numSeg:])
        earliestSoFarEndTime = sys.float_info.max
        solutions[str(numSeg)] = [{}]
        for sol in reversed(choices):
            if max(sol) - min(sol) < max(sol)*0.1 and max(sol) != min(sol):
                continue
            segs = tuple(reversed(sol))
            latestEndTime = -1
            deploy = []
            for lens in segs:
                #TODO: for machine in machine_list
                earliestStartTimeList = [findEarliestStartTimeFromDB(length ,machine, deploy) for machine in machine_list]
                pick_machine = np.argmin(earliestStartTimeList)
                earliestStartTime = (earliestStartTimeList[pick_machine] - totalStartTime.date()).days
                # bestSoFarNODESLIST.append(Node([],lens,pick_machine,-1,start=earliestStartTime,end=earliestStartTime+lens))
                if earliestStartTime + lens > latestEndTime:
                    latestEndTime = earliestStartTime + lens
                start = totalStartTime + datetime.timedelta(days=earliestStartTime)
                start = start.strftime('%Y-%m-%d')
                end = totalStartTime + datetime.timedelta(days=earliestStartTime + lens - 1)
                end = end.strftime('%Y-%m-%d')
                deploy.append({'start':start, 'length':str(lens), 'end':end, 'machine':str(machine_list[pick_machine])})
            # for i in range(len(segs)):
            #     bestSoFarNODESLIST.pop()
            if latestEndTime < earliestSoFarEndTime and latestEndTime <= deadline and not detectChain(deploy):
                earliestSoFarEndTime = latestEndTime
                solutions[str(numSeg)] = deploy
                dep_list = [n['end'] for n in deploy]
                jump=False
                for item in dep_list:
                    if dep_list.count(item) == numSeg-1 and numSeg != 2:
                        jump=True
                        break
                if jump:
                    del jump
                    break

    return solutions


def main(days:int, numSeg:int, start:str, deadline:str, clothNo:str) ->str:
    initialization()
    constructionPhase()
    solutions = getSolutions(numOfSegs=numSeg, taskLength=days, deadline=deadline, clothNo='WS-1234')
    result = JsonString()
    json.dump(solutions, result, indent=4)
    return result.get()
# print(main(days=10, numSeg=2, start=0, deadline=32, clothNo=0))
start = time()
initialization()
"""
    先把原先已排的製令當作Lock讀進bestSoFarNODESLIST，
    再從1台~N台一個一個找最佳解
"""
constructionPhase()

print('Schedule completed.')
print('Cost: %.2f seconds with %d ants, %d iterations'%(time()-start, K, C))
#%%
blocks = []
filled = 0
available = 0
for machine in range(numMachines):
    blocks.append([False]*max([i.endTime for i in bestSoFarNODESLIST if i.machine==machine], default=0))
    for node in [i for i in bestSoFarNODESLIST if i.machine==machine]:
        blocks[machine][node.startTime:node.endTime]=[True]*node.duration
    filled += sum(blocks[machine])
    available += len(blocks[machine])
total_density = filled/available
print('total density: %.5f\n'%total_density)
#%%
start = time()
solutions = getSolutions(numOfSegs=2, taskLength=10, deadline=32, clothNo='WS-1234')
print('Cost: %.2f seconds with %d segments'%(time()-start, 2))

# with open('solutions.json','w') as json_file:
#     json.dump(solutions, json_file, indent=4)

for i,sol in enumerate(solutions.values()):
    print('\nsolution %d with %d segments:'%(i+1, len(sol)))
    for dep in sol:
        print('    ', dep, sep='')

# =============================================================================
# conn = pymysql.connect('localhost', 'root', 'combo5210', 'wayson-dev-0901')
# 
# data = pd.read_sql_query("""SELECT weaving_machine_core_no
#                             FROM cloth_core
#                             	INNER JOIN cloth_tissue
#                             	ON cloth_core.cloth_tissue_id = cloth_tissue.cloth_tissue_id
#                             	INNER  JOIN weaving_machine_core
#                             	ON cloth_tissue.fit_machine_type = weaving_machine_core.machine_type
#                             WHERE cloth_core.cloth_no='WS-1234'""",conn)
# machine_list = data.iloc[:,0].to_list()
# =============================================================================
'''
Idea for interface:
When an ant moves to a node, add dependency to node it's moving from if it's not already a dependent.
Give node a position propery for matrix. e.g., node.matrixPosition = [i][j] #look into paper about using modulus
'''