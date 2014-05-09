# search.py
# ---------
# Licensing Information: Please do not distribute or publish solutions to this
# project. You are free to use and extend these projects for educational
# purposes. The Pacman AI projects were developed at UC Berkeley, primarily by
# John DeNero (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# For more info, see http://inst.eecs.berkeley.edu/~cs188/sp09/pacman.html

"""
In search.py, you will implement generic search algorithms which are called
by Pacman agents (in searchAgents.py).
"""

import util
import searchAgents

#NO se implementa
class SearchProblem:
    """
    This class outlines the structure of a search problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the search problem
        """
        util.raiseNotDefined()

    def isGoalState(self, state):
        """
          state: Search state

        Returns True if and only if the state is a valid goal state
        """
        util.raiseNotDefined()

    def getSuccessors(self, state):
        """
          state: Search state

        For a given state, this should return a list of triples,
        (successor, action, stepCost), where 'successor' is a
        successor to the current state, 'action' is the action
        required to get there, and 'stepCost' is the incremental
        cost of expanding to that successor
        """
        util.raiseNotDefined()

    def getCostOfActions(self, actions):
        """
         actions: A list of actions to take

        This method returns the total cost of a particular sequence of actions.  The sequence must
        be composed of legal moves
        """
        util.raiseNotDefined()


def tinyMazeSearch(problem):
    """
    Returns a sequence of moves that solves tinyMaze.  For any other
    maze, the sequence of moves will be incorrect, so only use this for tinyMaze
    """
    from game import Directions
    s = Directions.SOUTH
    w = Directions.WEST
    return  [s,s,w,s,w,w,s,w]

#Hay que usar esta función
def search(problem, fringe):
    initial_state = problem.getStartState()
    initial_actions = []
    initial_candidate = (initial_state, initial_actions)
    fringe.push(initial_candidate)
    closed_set = set()
    while not fringe.isEmpty():
        candidate = fringe.pop()
        state, actions = candidate
        if problem.isGoalState(state):
            return actions
        if state not in closed_set:
            closed_set.add(state)
            candidate_successors = problem.getSuccessors(state)
            candidate_successors = filter(lambda x: x[0] not in closed_set, candidate_successors)
            candidate_successors = map(lambda x: (x[0], actions + [x[1]]), candidate_successors)
            for candidate in candidate_successors:
                fringe.push(candidate)

class Node:
    def __init__(self, state):
        self.state = state
        self.parentNode = None
        self.action = "None"
        self.wayCost = 0
        self.depth = 0

    def printNode(self):
        print "state: ", self.state
        print "parentNode: ", self.parentNode
        print "action: ", self.action
        print "wayCost: ", self.wayCost
        print "depth: ", self.depth

    def getCost(self):
        return self.wayCost

    def getDepth(self):
        return self.depth

    def getState(self):
        return self.state

    def getAction(self):
        return self.action

    def getParent(self):
        return self.parentNode

    def settingNode(self, parent, successor):
        self.state = successor[0]
        self.parentNode = parent
        self.action = successor[1]
        self.wayCost = parent.getCost() + successor[2]
        self.depth = parent.getDepth() + 1


def searchTree(problem, boundary):
    boundary.push(Node(problem.getStartState()))
    while True:
        if boundary.isEmpty():
            return [] #fallo
        node = boundary.pop()
        print "\n", node.printNode(), "\n"
        if problem.isGoalState(node.getState()):
            print "\nsolution :\n",solution(node),"\n"
            return solution(node)
        expand(problem, node, boundary)

def searchGraph(problem, boundary):
    closed = set()
    boundary.push(Node(problem.getStartState()))
    while True:
        if boundary.isEmpty():
            return []
        node = boundary.pop()
        print "\n", node.printNode(), "\n"
        if problem.isGoalState(node.getState()):
            print "\nsolution :\n",solution(node),"\n"
            return solution(node)
        if node.getState() not in closed:
            closed.add(node.getState())
            expand(problem, node, boundary)

def expand(problem, parentNode, boundary):
    for successor in problem.getSuccessors(parentNode.getState()):
        #print "\nsucesores: ",successor, "\n"
        #nose si se puede llamar con None
        childNode = Node(None)
        childNode.settingNode(parentNode, successor)
        #childNode.printNode()
        boundary.push(childNode)


def searchGraphWithFn(problem, boundary, f):
    closed = set()
   
    #f = lambda n: n.getCost() + h(n.getState(), problem)

    node = Node(problem.getStartState()) 
    boundary.push(node, f(node))
    while True:
        if boundary.isEmpty():
            return []
        node = boundary.pop()
        print "\n", node.printNode(), "\n"
        if problem.isGoalState(node.getState()):
            print "\nsolution :\n",solution(node),"\n"
            return solution(node)
        if node.getState() not in closed:
            closed.add(node.getState())
            expandWithFn(problem, node, boundary, f)



def expandWithFn(problem, parentNode, boundary, f):
    for successor in problem.getSuccessors(parentNode.getState()):
        #print "\nsucesores: ",successor, "\n"
        #nose si se puede llamar con None
        childNode = Node(None)
        childNode.settingNode(parentNode, successor)
        #childNode.printNode()
        boundary.push(childNode, f(childNode))


def solution(node):
    actions = []
    while node != None:
        # print "\n", p.printNode(), "\n"
        action = node.getAction()
        if action != "None":
            actions = [action] + actions
        node = node.getParent()
    return actions



def depthFirstSearch(problem):
    """
    Search the deepest nodes in the search tree first

    Your search algorithm needs to return a list of actions that reaches
    the goal.  Make sure to implement a graph search algorithm

    To get started, you might want to try some of these simple commands to
    understand the search problem that is being passed in:
    
    print "Start:", problem.getStartState()
    print "Is the start a goal?", problem.isGoalState(problem.getStartState())
    print "Start's successors:", problem.getSuccessors(problem.getStartState())
    """
    return search(problem, util.Stack())


def breadthFirstSearch(problem):
    """
    Search the shallowest nodes in the search tree first.
    """
    return search(problem, util.Queue())


def uniformCostSearch(problem):
    "Search the node of least total cost first."
    return searchGraphWithFn(problem, util.PriorityQueue(), nullHeuristic)
    


def nullHeuristic(state, problem=None):
    """
    A heuristic function estimates the cost from the current state to the nearest
    goal in the provided SearchProblem.  This heuristic is trivial.
    """
    return 0

def aStarSearch(problem, heuristic):
    "Search the node that has the lowest combined cost and heuristic first."
    f = lambda n: (n.getCost() + heuristic(n.getState(), problem))
    return searchGraphWithFn(problem, util.PriorityQueue(),f)
    

# Abbreviations
bfs = breadthFirstSearch
dfs = depthFirstSearch
astar = aStarSearch
ucs = uniformCostSearch
