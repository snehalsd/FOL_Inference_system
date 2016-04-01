import copy
import sys
log=[]
lastStatement=''
standardizeValue=0
class KB:
    def __init__(self,getclauses):#populate the Knowledge Base
        self.clauses=[]
        for eachClause in getclauses:
            self.clauses.append(eachClause)
    def getvalues(self):
        print self.clauses
    def FetchRulesForGoal(self,goal):# for each goal, see if the predicate of the goal matches the predicate of the rhs of any of the rules, return those rules
        parenthesis_start_index=goal.find("(")
        predicateGoal=goal[0:parenthesis_start_index]
        matchedClauses=[]
        for clause in self.clauses:
            splitClause=clause.strip().split(" => ");
            
            if(len(splitClause)==1):
                index=0
            else:
                index=1
            possible_goal_index=splitClause[index].find("(")
            predicatePossibleGoal=splitClause[index][0:possible_goal_index]
            if(predicateGoal==predicatePossibleGoal):
                matchedClauses.append(clause)
        return matchedClauses 
input=open(sys.argv[-1],"r")# read the file
querylist=list()
query=input.readline().strip()#get the query
querylist=query.split(" && ")#if of the for p && q
numofclauses=int(input.readline().strip())#number of clauses
inputclause=[]
while numofclauses > 0:#change variables to avoid clash AKA standardizing variables and append the clauses to the list
    line=input.readline().strip()
    inputclause.append(line)
    numofclauses-=1
knowledgeBase=KB(inputclause)#KnowledgeBase populated
file_handler = open('output.txt', 'w+')
def standardizeVariable(rule):
    global standardizeValue
    remaining = rule[:]
    newRule = ''
    openParanthesis = remaining.find('(')
    closeParanthesis = remaining.find(')')

    while (openParanthesis != -1 and closeParanthesis != -1):
        newRule = newRule + remaining[0:openParanthesis]
        remaining = remaining[closeParanthesis+1:]
        variable_list =remaining[openParanthesis+1:closeParanthesis].split(',')

        subsVar = ''
        for l in range (0,len(variables)):
            variables[l] = variables[l].strip()
            if ord(str(variables[l][0])) >= 97:
                subsVar = subsVar + variables[l]+''+str(standardizeCount)+', '
            else:
                subsVar = subsVar + variables[l] + ', '


        subsVar = '(' + subsVar[0:len(subsVar)-2] + ')'
        newRule = newRule + subsVar

        openIndex = remaining.find('(')
        closeIndex = remaining.find(')')

    lhs,rhs = getLHSnRHS(newRule)
    standardizeCount = standardizeCount + 1

    return lhs,rhs

def write_into_file(value):
    file_handler = open('output.txt', 'a')
    file_handler.write(value)
    file_handler.close()
def UpdateIfVariable(goal,theta):#if the parameters are variables and no value in theta, replace with underscore else with the value of that key in theta
    openParenthesis=goal.find("(")
    closeParenthesis=goal.find(")")
    variable_list=goal[openParenthesis+1:closeParenthesis].split(', ')
    predicate=goal[0:openParenthesis]
    substitution=''
    for var in range(0,len(variable_list)):
        variable_list[var]=variable_list[var].strip()
        if variable_list[var].islower():
            if(theta.has_key(variable_list[var])):
                substitute_with=str(theta[variable_list[var]])
                while substitute_with.islower() and theta.has_key(substitute_with):
                    substitute_with=str(theta[substitute_with])
                substitution=substitution+substitute_with+', '
            else:
                substitution=substitution+'_, '
        else:
            substitution=substitution+variable_list[var]+', '
    predicate=predicate+"("+substitution[0:len(substitution)-2]+ ")"
    return predicate
def UpdateThetaChanges(rhs,theta):
    openParenthesis=rhs.find("(")
    closeParenthesis=rhs.find(")")
    variable_list=rhs[openParenthesis+1:closeParenthesis].split(', ')
    predicate=rhs[0:openParenthesis]
    substitution=''
    for var in range(0,len(variable_list)):
        variable_list[var]=variable_list[var].strip()
        if variable_list[var].islower(): #and theta.has_key(variable_list[var]):
            substitute_with=str(theta[variable_list[var]])
            while substitute_with.islower():# and theta.has_key(substitute_with):
                substitute_with=str(theta[substitute_with])
            substitution=substitution+substitute_with+', '
        else:
            substitution=substitution+variable_list[var]+', '
    predicate=predicate+"("+substitution[0:len(substitution)-2]+ ")"
    return predicate  
def getLHSnRHS(rule):
    lhs=''
    rhs=''
    splitrule=rule.split(" => ")
    if(len(splitrule)==1):
        rhs=splitrule[0]
    else:
        lhs=splitrule[0]
        rhs=splitrule[1]
    return lhs,rhs

def getFirstAndRestGoals(goals):
    first=''
    rest=''
    partitiongoals=goals.partition(" && ")
    first=partitiongoals[0]
    if(len(partitiongoals)>1):
        rest=partitiongoals[2]
    return first,rest
def isCompound(x):
    if x.find("(")!=-1:
        return True
    else:
        False
def isList(value):
    if isVariable(value) or isCompound(value):
        return False
    elif str(value).find(',') != -1:
        return True
    else:
        return False
def isVariable(x):
    if x.find("(") == -1:
        if x.find(",") == -1:
            if x.islower():
                return True
    else:
        return False
def subst(theta,first):
    open_Parenthesis= first.find('(')
    close_Parenthesis = first.find(')')
    variables = first[open_Parenthesis+1:close_Parenthesis]
    variables = variables.split(',')
    substitution = ''
    for indexed in range (0,len(variables)):
        variables[indexed] = variables[indexed].strip()
        if str(variables[indexed][0]).islower() and theta.has_key(variables[indexed]):
            substitution = substitution + theta[variables[indexed]]+', '
        else:
            substitution = substitution + variables[indexed] + ', '

    substitution = first[0:open_Parenthesis+1]+substitution[0:len(substitution)-2] + ')'
    return substitution
def Unify_Var(var, x, theta):
    theta = copy.deepcopy(theta)
    if theta.has_key(var):
        return Unify(theta[var], x, theta)
    elif theta.has_key(x):
        return Unify(var, theta[x], theta)
    else:
        theta[var] = x
        return theta
def Unify(x,y,theta):
    theta = copy.deepcopy(theta)
    if theta=="failure":
        return "failure"
    elif x==y:
        return theta
    elif isVariable(x):
        return Unify_Var(x, y, theta)
    elif isVariable(y):
        return Unify_Var(y, x, theta)
    elif isCompound(x) and isCompound(y):
        return Unify(x[x.find("(")+1:x.find(")")],y[y.find("(")+1:y.find(")")],Unify(x[0:x.find("(")], y[0:y.find("(")], theta))
    elif isList(x) and isList(y):
        return Unify(x.partition(", ")[2],y.partition(", ")[2], Unify(x.partition(", ")[0], y.partition(", ")[0], theta))
    else:
        return 'failure'       
def FOL_BC_ASK(knowledgeBase,query):
    return FOL_BC_OR(knowledgeBase,query,{})
def FOL_BC_OR(knowledgeBase,goal,theta):
    rule_count=0
    Check_yield= False
    global log
    global lastStatement
    number_of_rules_fetched=len(knowledgeBase.FetchRulesForGoal(goal))
    prints=UpdateIfVariable(goal,theta)
    for rule in knowledgeBase.FetchRulesForGoal(goal):
        rule_count=rule_count+1
        currentPrint= 'Ask: '+prints
        if lastStatement!=currentPrint:
            if log.count(currentPrint)!=0:
                lhs,rhs=getLHSnRHS(rule) 
                if Unify(rhs,goal,theta)!= "failure":
                    write_into_file("Ask: "+prints+"\n")
                    lastStatement=currentPrint
                    log.append(currentPrint)
            else:
                write_into_file('Ask: '+prints+"\n")
                lastStatement=currentPrint
                log.append(currentPrint)   
        lhs,rhs=standardizeVariable(rule)
        for theta1 in FOL_BC_AND(knowledgeBase,lhs,Unify(rhs,goal,theta),rhs):
            Check_yield=True
            yield theta1
        if rule_count==number_of_rules_fetched and Check_yield==False:
            write_into_file("False: "+prints+"\n")
def FOL_BC_AND(knowledgeBase,goals,theta,rhs):
    if theta=="failure":
        return
    elif len(goals)==0:
        prints=UpdateThetaChanges(rhs,theta)
        write_into_file("True: "+prints+"\n")
        yield theta
    else:
        first,rest=getFirstAndRestGoals(goals)
        for theta1 in FOL_BC_OR(knowledgeBase,subst(theta,first),theta):
            for theta2 in FOL_BC_AND(knowledgeBase,rest,theta1,rhs):
                yield theta2
result= True
for query in querylist:
    log=[]
    lastStatement=''
    answer=FOL_BC_ASK(knowledgeBase,query)
    try:
        answer_list=next(answer)
        #print log
        result= True
    except StopIteration:
        #print log
        result=False
if result:
    write_into_file("True")
else:
    write_into_file("False")  