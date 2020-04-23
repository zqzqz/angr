import angr
import sys
import logging
from angr import global_apis
logging.getLogger('angr').setLevel('WARN')

example = sys.argv[1]
project = angr.Project("examples/{}/{}".format(example, example), load_options={'auto_load_libs': False})
# cfg = project.analyses.CFGFast()
# points_to = project.analyses.PointsTo()

state = project.factory.entry_state()
sm = project.factory.simulation_manager(state)
sm.run(until=lambda sm_: len(sm_.active) > 1)
# sm.run()
input_0 = sm.active[0].posix.dumps(0)
input_1 = sm.active[1].posix.dumps(0)

# for b in global_apis.VEX_IR:
#     print("=================")
#     for node in b:
#         for s in node.statements:
#             print(s)

print("Solution to enter the branch:", input_0)
if int(input_0) == 1:
    print("Correct!")
else:
    print("Something wrong!")