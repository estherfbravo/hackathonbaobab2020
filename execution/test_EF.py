from pyomo.environ import *
from random import randint, randrange


def get_assign_tasks_model():
    # Model definition
    model = AbstractModel()

    # Model sets definition
    model.sJobs = Set()
    model.sModes = Set()
    model.sResources = Set()
    model.sSlots = Set()

    # Model parameters definition
    model.pNumberSlots = Param(mutable=True)  # TODO comprobar si hace falta
    model.pDuration = Param(model.sJobs, model.sModes, mutable=True)
    model.pNeeds = Param(model.sJobs, model.sModes, model.sResources, mutable=True)
    model.pAvailability = Param(model.sResources, mutable=True)
    model.pResourceType = Param(model.sResources, mutable=True)  # TODO Habría que definir de que tipo es cada recurso
    model.p01Successor = Param(model.sJobs, model.sJobs, mutable=True, domain=Binary)
    model.pSlot = Param(model.sSlots, mutable=True)  # TODO comprobar si es necesario para sustituir a ord(iSlot)
    # pSlot[1] = 1, pSlot[2] = 2, ... habrá que definirlo

    # Model variables definition
    model.v01Start = Var(model.sJobs, model.sSlots, domain=Binary)
    model.v01End = Var(model.sJobs, model.sSlots, domain=Binary)
    model.v01JobDone = Var(model.sJobs, model.sSlots, model.sModes, domain=Binary)
    model.v01JobMode = Var(model.sJobs, model.sModes, domain=Binary)
    model.vMaxSlot = Var(domain=NonNegativeIntegers)

    # Model constraint definition
    # c1: the start time of a task should be earlier than the end time
    def c1_start_before_end(model, iJob):
        return sum(model.v01End[iJob, iSlot] * model.pSlot[iSlot] for iSlot in model.sSlots)\
               >= sum(model.v01Start[iJob, iSlot] * model.pSlot[iSlot] for iSlot in model.sSlots)

    # c2: the renewable resources used during each period should be inferior to the resource availability
    def c2_renewable_resources(model, iSlot, iResource, iMode):
        if model.pResourceType[iResource] == 1:
            return sum(model.v01JobDone[iJob, iSlot, iMode] * model.pNeeds[iJob, iMode, iResource]
                       for iJob in model.sJobs) <= model.pAvailability[iResource]
        return Constraint.Skip

    # c3: the total non renewable resources used should be inferior to the resource availability
    def c3_non_renewable_resources(model, iResource, iMode):
        if model.pResourceType[iResource] == 2:
            return sum(model.v01JobDone[iJob, iSlot, iMode] * model.pNeeds[iJob, iMode, iResource]
                       for iJob in model.sJobs for iSlot in model.sSlots) <= model.pAvailability[iResource]
        return Constraint.Skip

    # c4: precedence between tasks should be respected
    def c4_precedence(model, iJob, iJob2):
        if iJob != iJob2:
            return sum(model.v01Start[iJob2, iSlot] * model.pSlot[iSlot] for iSlot in model.sSlots)\
                   >= (sum(model.v01End[iJob, iSlot] * model.pSlot[iSlot] for iSlot in model.sSlots) + 1) \
                   * model.p01Successor[iJob, iJob2]
        return Constraint.Skip

    # c5: the number of slots in which the job is done should be equal to the job duration
    def c5_duration(model, iJob, iMode):
        return sum(model.v01JobDone[iJob, iSlot, iMode] for iSlot in model.sSlots) == model.pDuration[iJob, iMode] \
               * model.v01JobMode[iJob, iMode]

    # c6: the difference between the start and the end of a job is equal to its duration
    def c6_duration2(model, iJob):
        return sum(model.v01End[iJob, iSlot] * model.pSlot[iSlot] for iSlot in model.sSlots) \
               - sum(model.v01Start[iJob, iSlot] * model.pSlot[iSlot] for iSlot in model.sSlots) \
               == sum(model.v01JobMode[iJob, iMode] * model.pDuration[iJob, iMode] for iMode in model.sModes) - 1

    # c7: if a job ends in slot S, then the job is done in slot S but it is not done in slot S+1
    def c7_end_continuity(model, iJob, iSlot, iMode):
        if model.pSlot[iSlot] != model.pNumberSlots:  # TODO ver si funciona con ord(iSlot)
            return model.v01JobDone[iJob, iSlot, iMode] \
                   <= model.v01JobDone[iJob, str(int(iSlot)+1), iMode] + model.v01End[iJob, iSlot]
        return Constraint.Skip

    # c8: if a job starts in slot S+1, then the job is done in slot S+1 but it is not done in slot S
    def c8_start_continuity(model, iJob, iSlot, iMode):  # TODO ver si funciona con ord(iSlot), sino pSlot[iSlot]
        if model.pSlot[iSlot] != model.pNumberSlots:
            return model.v01JobDone[iJob, str(int(iSlot)+1), iMode] \
                   <= model.v01JobDone[iJob, iSlot, iMode] + model.v01Start[iJob, str(int(iSlot)+1)]
        return Constraint.Skip

    # c9: the job can only start once
    def c9_one_start(model, iJob):
        return sum(model.v01Start[iJob, iSlot] for iSlot in model.sSlots) == 1

    # c10: the job can only end once
    def c10_one_end(model, iJob):
        return sum(model.v01End[iJob, iSlot] for iSlot in model.sSlots) == 1

    # c11: only one mode can be used for each job
    def c11_one_mode(model, iJob):
        return sum(model.v01JobMode[iJob, iMode] for iMode in model.sModes) == 1

    # c12: is a job J is done in a slot with mode M, then it means mode M is used for job J
    def c12_job_mode(model, iJob, iSlot, iMode):
        return model.v01JobMode[iJob, iMode] >= model.v01JobDone[iJob, iSlot, iMode]

    # c13: the variable to be minimized is the latest ending time
    def c13_total_duration(model, iJob, iSlot):
        return model.v01End[iJob, iSlot] * model.pSlot[iSlot] <= model.vMaxSlot

    # Activate constraints
    model.c1_start_before_end = Constraint(model.sJobs, rule=c1_start_before_end)
    model.c2_renewable_resources = Constraint(model.sSlots, model.sResources, model.sModes, rule=c2_renewable_resources)
    model.c3_non_renewable_resources = Constraint(model.sResources, model.sModes, rule=c3_non_renewable_resources)
    model.c4_precedence = Constraint(model.sJobs, model.sJobs, rule=c4_precedence)
    model.c5_duration = Constraint(model.sJobs, model.sModes, rule=c5_duration)
    model.c6_duration2 = Constraint(model.sJobs, rule=c6_duration2)
    model.c7_end_continuity = Constraint(model.sJobs, model.sSlots, model.sModes, rule=c7_end_continuity)
    model.c8_start_continuity = Constraint(model.sJobs, model.sSlots, model.sModes, rule=c8_start_continuity)
    model.c9_one_start = Constraint(model.sJobs, rule=c9_one_start)
    model.c10_one_end = Constraint(model.sJobs, rule=c10_one_end)
    model.c11_one_mode = Constraint(model.sJobs, rule=c11_one_mode)
    model.c12_job_mode = Constraint(model.sJobs, model.sSlots, model.sModes, rule=c12_job_mode)
    model.c13_total_duration = Constraint(model.sJobs, model.sSlots, rule=c13_total_duration)

    # Objective function definition
    def obj_expression(model):
        return model.vMaxSlot

    # Activate objective function
    model.f_obj = Objective(rule=obj_expression, sense=minimize)

    return model


# Example dataset 1
def get_assign_task_model_test_data_1():

    assign_tasks_model_data = dict()

    # Sets data
    assign_tasks_model_data['sJobs'] = {None: {"J1", "J2", "J3"}}
    assign_tasks_model_data['sModes'] = {None: {"M2"}}
    assign_tasks_model_data['sResources'] = {None: {"R1", "NR1"}}
    assign_tasks_model_data['sSlots'] = {None: {"1", "2", "3", "4", "5", "6", "7", "8", "9"}}

    # Parameters data
    assign_tasks_model_data['pNumberSlots'] = {None: 9}
    assign_tasks_model_data['pDuration'] = {("J1", "M1"): 2, ("J2", "M1"): 3, ("J3", "M1"): 4}
    assign_tasks_model_data['pNeeds'] = {("J1", "M1", "R1"): 3, ("J2", "M1", "R1"): 3, ("J3", "M1", "R1"): 3,
                                         ("J1", "M1", "NR1"): 5, ("J2", "M1", "NR1"): 5, ("J3", "M1", "NR1"): 5}
    assign_tasks_model_data['pAvailability'] = {"R1": 100, "NR1": 100}
    assign_tasks_model_data['pResourceType'] = {"R1": 1, "NR1": 2}
    assign_tasks_model_data['p01Successor'] = {("J1", "J1"): 0, ("J1", "J2"): 1, ("J1", "J3"): 0, ("J2", "J1"): 0,
                                               ("J2", "J2"): 0, ("J2", "J3"): 1, ("J3", "J1"): 0, ("J3", "J2"): 0,
                                               ("J3", "J3"): 0}
    assign_tasks_model_data['pSlot'] = {"1": 1, "2": 2, "3": 3, "4": 4, "5": 5, "6": 6, "7": 7, "8": 8, "9": 9}

    return {None: assign_tasks_model_data}


# Example dataset 2
def get_assign_task_model_test_data_2():

    assign_tasks_model_data = dict()

    # Sets data
    assign_tasks_model_data['sJobs'] = {None: {"J1", "J2", "J3"}}
    assign_tasks_model_data['sModes'] = {None: {"M1", "M2"}}
    assign_tasks_model_data['sResources'] = {None: {"R1", "NR1"}}
    assign_tasks_model_data['sSlots'] = {None: {"1", "2", "3", "4", "5", "6", "7", "8", "9"}}

    # Parameters data
    assign_tasks_model_data['pNumberSlots'] = {None: 9}
    assign_tasks_model_data['pDuration'] = {("J1", "M1"): 2, ("J2", "M1"): 3, ("J3", "M1"): 4, ("J1", "M2"): 3,
                                            ("J2", "M2"): 2, ("J3", "M2"): 2}
    assign_tasks_model_data['pNeeds'] = {("J1", "M1", "R1"): 3, ("J2", "M1", "R1"): 3, ("J3", "M1", "R1"): 3,
                                         ("J1", "M1", "NR1"): 5, ("J2", "M1", "NR1"): 5, ("J3", "M1", "NR1"): 5,
                                         ("J1", "M2", "R1"): 3, ("J2", "M2", "R1"): 3, ("J3", "M2", "R1"): 3,
                                         ("J1", "M2", "NR1"): 5, ("J2", "M2", "NR1"): 5, ("J3", "M2", "NR1"): 5}
    assign_tasks_model_data['pAvailability'] = {"R1": 100, "NR1": 100}
    assign_tasks_model_data['pResourceType'] = {"R1": 1, "NR1": 2}
    assign_tasks_model_data['p01Successor'] = {("J1", "J1"): 0, ("J1", "J2"): 1, ("J1", "J3"): 0, ("J2", "J1"): 0,
                                               ("J2", "J2"): 0, ("J2", "J3"): 1, ("J3", "J1"): 0, ("J3", "J2"): 0,
                                               ("J3", "J3"): 0}
    assign_tasks_model_data['pSlot'] = {"1": 1, "2": 2, "3": 3, "4": 4, "5": 5, "6": 6, "7": 7, "8": 8, "9": 9}

    return {None: assign_tasks_model_data}


# Example dataset 3
def get_assign_task_model_test_data_3():

    assign_tasks_model_data = dict()

    # Sets data
    assign_tasks_model_data['sJobs'] = {None: {"J1", "J2", "J3", "J4", "J5", "J6", "J7", "J8", "J9", "J10", "J11",
                                               "J12", "J13", "J14", "J15", "J16", "J17", "J18"}}
    assign_tasks_model_data['sModes'] = {None: {"M1", "M2"}}
    assign_tasks_model_data['sResources'] = {None: {"R1", "R2", "NR1", "NR2"}}
    assign_tasks_model_data['sSlots'] = {None: {"1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13",
                                                "14", "15", "16", "17", "18", "19", "20", "21", "22", "23", "24", "25",
                                                "26", "27", "28", "29", "30"}}  # TODO cambiar con element range

    # Parameters data
    assign_tasks_model_data['pNumberSlots'] = {None: 30}
    assign_tasks_model_data['pDuration'] = {("J1", "M1"): randint(1,4), ("J2", "M1"): randint(1,4), ("J3", "M1"): randint(1,4), ("J4", "M1"): randint(1,4),
                                            ("J5", "M1"): randint(1,4), ("J6", "M1"): randint(1,4), ("J7", "M1"): randint(1,4), ("J8", "M1"): randint(1,4),
                                            ("J9", "M1"): randint(1,4), ("J10", "M1"): randint(1,4), ("J11", "M1"): randint(1,4), ("J12", "M1"): randint(1,4),
                                            ("J13", "M1"): randint(1,4), ("J14", "M1"): randint(1,4), ("J15", "M1"): randint(1,4), ("J16", "M1"): randint(1,4),
                                            ("J17", "M1"): randint(1,4), ("J18", "M1"): randint(1,4), ("J1", "M2"): randint(1,4), ("J2", "M2"): randint(1,4),
                                            ("J3", "M2"): randint(1,4), ("J4", "M2"): randint(1,4), ("J5", "M2"): randint(1,4), ("J6", "M2"): randint(1,4),
                                            ("J7", "M2"): randint(1,4), ("J8", "M2"): randint(1,4), ("J9", "M2"): randint(1,4), ("J10", "M2"): randint(1,4),
                                            ("J11", "M2"): randint(1,4), ("J12", "M2"): randint(1,4), ("J13", "M2"): randint(1,4), ("J14", "M2"): randint(1,4),
                                            ("J15", "M2"): randint(1,4), ("J16", "M2"): randint(1,4), ("J17", "M2"): randint(1,4), ("J18", "M2"): randint(1,4)}
    assign_tasks_model_data['pNeeds'] = {("J1", "M1", "R1"): randint(1,4), ("J2", "M1", "R1"): randint(1,4), ("J3", "M1", "R1"): randint(1,4),
                                         ("J4", "M1", "R1"): randint(1,4), ("J5", "M1", "R1"): randint(1,4), ("J6", "M1", "R1"): randint(1,4),
                                         ("J7", "M1", "R1"): randint(1,4), ("J8", "M1", "R1"): randint(1,4), ("J9", "M1", "R1"): randint(1,4),
                                         ("J10", "M1", "R1"): randint(1,4), ("J11", "M1", "R1"): randint(1,4), ("J12", "M1", "R1"): randint(1,4),
                                         ("J13", "M1", "R1"): randint(1,4), ("J14", "M1", "R1"): randint(1,4), ("J15", "M1", "R1"): randint(1,4),
                                         ("J16", "M1", "R1"): randint(1,4), ("J17", "M1", "R1"): randint(1,4), ("J18", "M1", "R1"): randint(1,4),

                                         ("J1", "M1", "R2"): randint(1,4), ("J2", "M1", "R2"): randint(1,4), ("J3", "M1", "R2"): randint(1,4),
                                         ("J4", "M1", "R2"): randint(1,4), ("J5", "M1", "R2"): randint(1,4), ("J6", "M1", "R2"): randint(1,4),
                                         ("J7", "M1", "R2"): randint(1,4), ("J8", "M1", "R2"): randint(1,4), ("J9", "M1", "R2"): randint(1,4),
                                         ("J10", "M1", "R2"): randint(1,4), ("J11", "M1", "R2"): randint(1,4), ("J12", "M1", "R2"): randint(1,4),
                                         ("J13", "M1", "R2"): randint(1,4), ("J14", "M1", "R2"): randint(1,4), ("J15", "M1", "R2"): randint(1,4),
                                         ("J16", "M1", "R2"): randint(1,4), ("J17", "M1", "R2"): randint(1,4), ("J18", "M1", "R2"): randint(1,4),

                                         ("J1", "M1", "NR1"): randint(1,4), ("J2", "M1", "NR1"): randint(1,4), ("J3", "M1", "NR1"): randint(1,4),
                                         ("J4", "M1", "NR1"): randint(1,4), ("J5", "M1", "NR1"): randint(1,4), ("J6", "M1", "NR1"): randint(1,4),
                                         ("J7", "M1", "NR1"): randint(1,4), ("J8", "M1", "NR1"): randint(1,4), ("J9", "M1", "NR1"): randint(1,4),
                                         ("J10", "M1", "NR1"): randint(1,4), ("J11", "M1", "NR1"): randint(1,4), ("J12", "M1", "NR1"): randint(1,4),
                                         ("J13", "M1", "NR1"): randint(1,4), ("J14", "M1", "NR1"): randint(1,4), ("J15", "M1", "NR1"): randint(1,4),
                                         ("J16", "M1", "NR1"): randint(1,4), ("J17", "M1", "NR1"): randint(1,4), ("J18", "M1", "NR1"): randint(1,4),

                                         ("J1", "M1", "NR2"): randint(1,4), ("J2", "M1", "NR2"): randint(1,4), ("J3", "M1", "NR2"): randint(1,4),
                                         ("J4", "M1", "NR2"): randint(1,4), ("J5", "M1", "NR2"): 3, ("J6", "M1", "NR2"): randint(1,4),
                                         ("J7", "M1", "NR2"): randint(1,4), ("J8", "M1", "NR2"): randint(1,4), ("J9", "M1", "NR2"): randint(1,4),
                                         ("J10", "M1", "NR2"): randint(1,4), ("J11", "M1", "NR2"): randint(1,4), ("J12", "M1", "NR2"): randint(1,4),
                                         ("J13", "M1", "NR2"): randint(1,4), ("J14", "M1", "NR2"): randint(1,4), ("J15", "M1", "NR2"): randint(1,4),
                                         ("J16", "M1", "NR2"): randint(1,4), ("J17", "M1", "NR2"): randint(1,4), ("J18", "M1", "NR2"): randint(1,4),

                                         ("J1", "M2", "R1"): randint(1,4), ("J2", "M2", "R1"): randint(1,4), ("J3", "M2", "R1"): randint(1,4),
                                         ("J4", "M2", "R1"): randint(1,4), ("J5", "M2", "R1"): randint(1,4), ("J6", "M2", "R1"): randint(1,4),
                                         ("J7", "M2", "R1"): randint(1,4), ("J8", "M2", "R1"): randint(1,4), ("J9", "M2", "R1"): randint(1,4),
                                         ("J10", "M2", "R1"): randint(1,4), ("J11", "M2", "R1"): randint(1,4), ("J12", "M2", "R1"): randint(1,4),
                                         ("J13", "M2", "R1"): randint(1,4), ("J14", "M2", "R1"): randint(1,4), ("J15", "M2", "R1"): randint(1,4),
                                         ("J16", "M2", "R1"): randint(1,4), ("J17", "M2", "R1"): randint(1,4), ("J18", "M2", "R1"): randint(1,4),

                                         ("J1", "M2", "R2"): randint(1,4), ("J2", "M2", "R2"): randint(1,4), ("J3", "M2", "R2"): randint(1,4),
                                         ("J4", "M2", "R2"): randint(1,4), ("J5", "M2", "R2"): randint(1,4), ("J6", "M2", "R2"): randint(1,4),
                                         ("J7", "M2", "R2"): randint(1,4), ("J8", "M2", "R2"): randint(1,4), ("J9", "M2", "R2"): randint(1,4),
                                         ("J10", "M2", "R2"): randint(1,4), ("J11", "M2", "R2"): randint(1,4), ("J12", "M2", "R2"): randint(1,4),
                                         ("J13", "M2", "R2"): randint(1,4), ("J14", "M2", "R2"): randint(1,4), ("J15", "M2", "R2"): randint(1,4),
                                         ("J16", "M2", "R2"): randint(1,4), ("J17", "M2", "R2"): randint(1,4), ("J18", "M2", "R2"): randint(1,4),

                                         ("J1", "M2", "NR1"): randint(1,4), ("J2", "M2", "NR1"): randint(1,4), ("J3", "M2", "NR1"): randint(1,4),
                                         ("J4", "M2", "NR1"): randint(1,4), ("J5", "M2", "NR1"): randint(1,4), ("J6", "M2", "NR1"): randint(1,4),
                                         ("J7", "M2", "NR1"): randint(1,4), ("J8", "M2", "NR1"): randint(1,4), ("J9", "M2", "NR1"): randint(1,4),
                                         ("J10", "M2", "NR1"): randint(1,4), ("J11", "M2", "NR1"): randint(1,4), ("J12", "M2", "NR1"): randint(1,4),
                                         ("J13", "M2", "NR1"): randint(1,4), ("J14", "M2", "NR1"): randint(1,4), ("J15", "M2", "NR1"): randint(1,4),
                                         ("J16", "M2", "NR1"): randint(1,4), ("J17", "M2", "NR1"): randint(1,4), ("J18", "M2", "NR1"): randint(1,4),

                                         ("J1", "M2", "NR2"): randint(1,4), ("J2", "M2", "NR2"): randint(1,4), ("J3", "M2", "NR2"): randint(1,4),
                                         ("J4", "M2", "NR2"): randint(1,4), ("J5", "M2", "NR2"): randint(1,4), ("J6", "M2", "NR2"): randint(1,4),
                                         ("J7", "M2", "NR2"): randint(1,4), ("J8", "M2", "NR2"): randint(1,4), ("J9", "M2", "NR2"): randint(1,4),
                                         ("J10", "M2", "NR2"): randint(1,4), ("J11", "M2", "NR2"): randint(1,4), ("J12", "M2", "NR2"): randint(1,4),
                                         ("J13", "M2", "NR2"): randint(1,4), ("J14", "M2", "NR2"): randint(1,4), ("J15", "M2", "NR2"): randint(1,4),
                                         ("J16", "M2", "NR2"): randint(1,4), ("J17", "M2", "NR2"): randint(1,4), ("J18", "M2", "NR2"): randint(1,4)}

    assign_tasks_model_data['pAvailability'] = {"R1": 100, "R2": 100, "NR1": 100, "NR2": 100}
    assign_tasks_model_data['pResourceType'] = {"R1": 1, "R2": 1, "NR1": 2, "NR2": 2}
    assign_tasks_model_data['p01Successor'] = {("J1", "J1"): 0, ("J1", "J2"): 1, ("J1", "J3"): 1, ("J1", "J4"): 1,
                                               ("J1", "J5"): 0, ("J1", "J6"): 0, ("J1", "J7"): 0, ("J1", "J8"): 0, 
                                               ("J1", "J9"): 0, ("J1", "J10"): 0, ("J1", "J11"): 0, ("J1", "J12"): 0, 
                                               ("J1", "J13"): 0, ("J1", "J14"): 0, ("J1", "J15"): 0, ("J1", "J16"): 0,
                                               ("J1", "J17"): 0, ("J1", "J18"): 0,

                                               ("J2", "J1"): 0, ("J2", "J2"): 0, ("J2", "J3"): 0, ("J2", "J4"): 0, 
                                               ("J2", "J5"): 1, ("J2", "J6"): 1, ("J2", "J7"): 0, ("J2", "J8"): 0,
                                               ("J2", "J9"): 1, ("J2", "J10"): 0, ("J2", "J11"): 0, ("J2", "J12"): 0,
                                               ("J2", "J13"): 0, ("J2", "J14"): 0, ("J2", "J15"): 0, ("J2", "J16"): 0,
                                               ("J2", "J17"): 0, ("J2", "J18"): 0,

                                               ("J3", "J1"): 0, ("J3", "J2"): 0, ("J3", "J3"): 0, ("J3", "J4"): 0,
                                               ("J3", "J5"): 1, ("J3", "J6"): 0, ("J3", "J7"): 0, ("J3", "J8"): 0,
                                               ("J3", "J9"): 0, ("J3", "J10"): 0, ("J3", "J11"): 0, ("J3", "J12"): 0,
                                               ("J3", "J13"): 0, ("J3", "J14"): 0, ("J3", "J15"): 0, ("J3", "J16"): 0,
                                               ("J3", "J17"): 0, ("J3", "J18"): 0,

                                               ("J4", "J1"): 0, ("J4", "J2"): 0, ("J4", "J3"): 0, ("J4", "J4"): 0,
                                               ("J4", "J5"): 0, ("J4", "J6"): 0, ("J4", "J7"): 0, ("J4", "J8"): 0,
                                               ("J4", "J9"): 0, ("J4", "J10"): 0, ("J4", "J11"): 1, ("J4", "J12"): 0,
                                               ("J4", "J13"): 0, ("J4", "J14"): 0, ("J4", "J15"): 1, ("J4", "J16"): 0,
                                               ("J4", "J17"): 0, ("J4", "J18"): 0,

                                               ("J5", "J1"): 0, ("J5", "J2"): 0, ("J5", "J3"): 0, ("J5", "J4"): 0,
                                               ("J5", "J5"): 0, ("J5", "J6"): 0, ("J5", "J7"): 0, ("J5", "J8"): 0,
                                               ("J5", "J9"): 0, ("J5", "J10"): 0, ("J5", "J11"): 0, ("J5", "J12"): 0,
                                               ("J5", "J13"): 0, ("J5", "J14"): 1, ("J5", "J15"): 0, ("J5", "J16"): 0,
                                               ("J5", "J17"): 0, ("J5", "J18"): 0,

                                               ("J6", "J1"): 0, ("J6", "J2"): 0, ("J6", "J3"): 0, ("J6", "J4"): 0,
                                               ("J6", "J5"): 0, ("J6", "J6"): 0, ("J6", "J7"): 1, ("J6", "J8"): 1,
                                               ("J6", "J9"): 0, ("J6", "J10"): 0, ("J6", "J11"): 0, ("J6", "J12"): 0,
                                               ("J6", "J13"): 1, ("J6", "J14"): 0, ("J6", "J15"): 0, ("J6", "J16"): 0,
                                               ("J6", "J17"): 0, ("J6", "J18"): 0,

                                               ("J7", "J1"): 0, ("J7", "J2"): 0, ("J7", "J3"): 0, ("J7", "J4"): 0,
                                               ("J7", "J5"): 0, ("J7", "J6"): 0, ("J7", "J7"): 0, ("J7", "J8"): 0,
                                               ("J7", "J9"): 0, ("J7", "J10"): 0, ("J7", "J11"): 0, ("J7", "J12"): 1,
                                               ("J7", "J13"): 0, ("J7", "J14"): 0, ("J7", "J15"): 0, ("J7", "J16"): 0,
                                               ("J7", "J17"): 0, ("J7", "J18"): 0,

                                               ("J8", "J1"): 0, ("J8", "J2"): 0, ("J8", "J3"): 0, ("J8", "J4"): 0,
                                               ("J8", "J5"): 0, ("J8", "J6"): 0, ("J8", "J7"): 0, ("J8", "J8"): 0,
                                               ("J8", "J9"): 0, ("J8", "J10"): 0, ("J8", "J11"): 0, ("J8", "J12"): 0,
                                               ("J8", "J13"): 0, ("J8", "J14"): 0, ("J8", "J15"): 1, ("J8", "J16"): 0,
                                               ("J8", "J17"): 1, ("J8", "J18"): 0,

                                               ("J9", "J1"): 0, ("J9", "J2"): 0, ("J9", "J3"): 0, ("J9", "J4"): 0,
                                               ("J9", "J5"): 0, ("J9", "J6"): 0, ("J9", "J7"): 0, ("J9", "J8"): 0,
                                               ("J9", "J9"): 0, ("J9", "J10"): 1, ("J9", "J11"): 0, ("J9", "J12"): 0,
                                               ("J9", "J13"): 0, ("J9", "J14"): 0, ("J9", "J15"): 0, ("J9", "J16"): 1,
                                               ("J9", "J17"): 0, ("J9", "J18"): 0,

                                               ("J10", "J1"): 0, ("J10", "J2"): 0, ("J10", "J3"): 0, ("J10", "J4"): 0,
                                               ("J10", "J5"): 0, ("J10", "J6"): 0, ("J10", "J7"): 0, ("J10", "J8"): 0,
                                               ("J10", "J9"): 0, ("J10", "J10"): 0, ("J10", "J11"): 1, ("J10", "J12"): 0,
                                               ("J10", "J13"): 0, ("J10", "J14"): 0, ("J10", "J15"): 1, ("J10", "J16"): 0,
                                               ("J10", "J17"): 0, ("J10", "J18"): 0,

                                               ("J11", "J1"): 0, ("J11", "J2"): 0, ("J11", "J3"): 0, ("J11", "J4"): 0,
                                               ("J11", "J5"): 0, ("J11", "J6"): 0, ("J11", "J7"): 0, ("J11", "J8"): 0,
                                               ("J11", "J9"): 0, ("J11", "J10"): 0, ("J11", "J11"): 0, ("J11", "J12"): 0,
                                               ("J11", "J13"): 0, ("J11", "J14"): 0, ("J11", "J15"): 0, ("J11", "J16"): 0,
                                               ("J11", "J17"): 1, ("J11", "J18"): 0,

                                               ("J12", "J1"): 0, ("J12", "J2"): 0, ("J12", "J3"): 0, ("J12", "J4"): 0,
                                               ("J12", "J5"): 0, ("J12", "J6"): 0, ("J12", "J7"): 0, ("J12", "J8"): 0,
                                               ("J12", "J9"): 0, ("J12", "J10"): 0, ("J12", "J11"): 0, ("J12", "J12"): 0,
                                               ("J12", "J13"): 0, ("J12", "J14"): 0, ("J12", "J15"): 0, ("J12", "J16"): 1,
                                               ("J12", "J17"): 0, ("J12", "J18"): 0,

                                               ("J13", "J1"): 0, ("J13", "J2"): 0, ("J13", "J3"): 0, ("J13", "J4"): 0,
                                               ("J13", "J5"): 0, ("J13", "J6"): 0, ("J13", "J7"): 0, ("J13", "J8"): 0,
                                               ("J13", "J9"): 0, ("J13", "J10"): 0, ("J13", "J11"): 0, ("J13", "J12"): 0,
                                               ("J13", "J13"): 0, ("J13", "J14"): 0, ("J13", "J15"): 0, ("J13", "J16"): 1,
                                               ("J13", "J17"): 0, ("J13", "J18"): 0,

                                               ("J14", "J1"): 0, ("J14", "J2"): 0, ("J14", "J3"): 0, ("J14", "J4"): 0,
                                               ("J14", "J5"): 0, ("J14", "J6"): 0, ("J14", "J7"): 0, ("J14", "J8"): 0,
                                               ("J14", "J9"): 0, ("J14", "J10"): 0, ("J14", "J11"): 0, ("J14", "J12"): 0,
                                               ("J14", "J13"): 0, ("J14", "J14"): 0, ("J14", "J15"): 0, ("J14", "J16"): 0,
                                               ("J14", "J17"): 1, ("J14", "J18"): 0,

                                               ("J15", "J1"): 0, ("J15", "J2"): 0, ("J15", "J3"): 0, ("J15", "J4"): 0,
                                               ("J15", "J5"): 0, ("J15", "J6"): 0, ("J15", "J7"): 0, ("J15", "J8"): 0,
                                               ("J15", "J9"): 0, ("J15", "J10"): 0, ("J15", "J11"): 0, ("J15", "J12"): 0,
                                               ("J15", "J13"): 0, ("J15", "J14"): 0, ("J15", "J15"): 0, ("J15", "J16"): 0,
                                               ("J15", "J17"): 0, ("J15", "J18"): 1,

                                               ("J16", "J1"): 0, ("J16", "J2"): 0, ("J16", "J3"): 0, ("J16", "J4"): 0,
                                               ("J16", "J5"): 0, ("J16", "J6"): 0, ("J16", "J7"): 0, ("J16", "J8"): 0,
                                               ("J16", "J9"): 0, ("J16", "J10"): 0, ("J16", "J11"): 0, ("J16", "J12"): 0,
                                               ("J16", "J13"): 0, ("J16", "J14"): 0, ("J16", "J15"): 0, ("J16", "J16"): 0,
                                               ("J16", "J17"): 0, ("J16", "J18"): 1,

                                               ("J17", "J1"): 0, ("J17", "J2"): 0, ("J17", "J3"): 0, ("J17", "J4"): 0,
                                               ("J17", "J5"): 0, ("J17", "J6"): 0, ("J17", "J7"): 0, ("J17", "J8"): 0,
                                               ("J17", "J9"): 0, ("J17", "J10"): 0, ("J17", "J11"): 0, ("J17", "J12"): 0,
                                               ("J17", "J13"): 0, ("J17", "J14"): 0, ("J17", "J15"): 0, ("J17", "J16"): 0,
                                               ("J17", "J17"): 0, ("J17", "J18"): 1,

                                               ("J18", "J1"): 0, ("J18", "J2"): 0, ("J18", "J3"): 0, ("J18", "J4"): 0,
                                               ("J18", "J5"): 0, ("J18", "J6"): 0, ("J18", "J7"): 0, ("J18", "J8"): 0,
                                               ("J18", "J9"): 0, ("J18", "J10"): 0, ("J18", "J11"): 0, ("J18", "J12"): 0,
                                               ("J18", "J13"): 0, ("J18", "J14"): 0, ("J18", "J15"): 0, ("J18", "J16"): 0,
                                               ("J18", "J17"): 0, ("J18", "J18"): 0}

    assign_tasks_model_data['pSlot'] = {"1": 1, "2": 2, "3": 3, "4": 4, "5": 5, "6": 6, "7": 7, "8": 8, "9": 9,
                                        "10": 10, "11": 11, "12": 12, "13": 13, "14": 14, "15": 15, "16": 16, "17": 17,
                                        "18": 18, "19": 19, "20": 20, "21": 21, "22": 22, "23": 23, "24": 24, "25": 25,
                                        "26": 26, "27": 27, "28": 28, "29": 29, "30": 30}

    return {None: assign_tasks_model_data}


# Build model
model = get_assign_tasks_model()

# Create instance 1
# instance1 = model.create_instance(get_assign_task_model_test_data_1())
# instance1.pprint()

# Create instance 2
# instance2 = model.create_instance(get_assign_task_model_test_data_2())
# instance2.pprint()

# Create instance 3
instance3 = model.create_instance(get_assign_task_model_test_data_3())
instance3.pprint()

# Include solver
opt = SolverFactory('cbc', executable="../solvers/cbc")
solver_parameters = {
    # maximum resolution time
    "sec": 1200,
    # accepted absolute gap
    "allow": 100,
    # accepted relative gap (0.01 = 1%)
    "ratio": 0.01,
    # Model tolerance
    "primalT": 10 ** -7
}

opt.options.update(solver_parameters)


# Solve instance 1
# result = opt.solve(instance1, tee=True)
# Print solution
# for i in instance1.sJobs:
#     for j in instance1.sSlots:
#         for k in instance1.sModes:
#             val1 = value(instance1.v01JobDone[i, j, k])
#             if val1 > 0:
#                 print("Jobs assigned", i, j, k, val1)

# Solve instance 2
# result = opt.solve(instance2, tee=True)
# Print solution
# for i in instance2.sJobs:
#     for j in instance2.sSlots:
#         for k in instance2.sModes:
#             val1 = value(instance2.v01JobDone[i, j, k])
#             if val1 > 0:
#                 print("Jobs assigned", i, j, k, val1)

# Solve instance 3
result = opt.solve(instance3, tee=True)

# Print solution
for i in instance3.sJobs:
    for j in instance3.sSlots:
        for k in instance3.sModes:
            val1 = value(instance3.v01JobDone[i, j, k])
            dur = value(instance3.pDuration[i, k])
            if val1 > 0:
                print("Jobs assigned", i, j, k, val1, "Duration", dur)

