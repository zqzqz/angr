import angr
import sys
import logging
logging.getLogger('angr').setLevel('DEBUG')

example = sys.argv[1]
points_to_preset = angr.misc.PluginPreset()
points_to_preset.add_default_plugin("points_to", angr.analyses.PointsTo())
project = angr.Project("examples/{}/{}".format(example, example), auto_load_libs=False, analyses_preset=points_to_preset)

state = project.factory.entry_state()
sm = project.factory.simulation_manager(state)
sm.run(until=lambda sm_: len(sm_.active) > 1)
input_0 = sm.active[0].posix.dumps(0)
input_1 = sm.active[1].posix.dumps(0)

print("Solution to enter the branch:", input_0)
if int(input_0) == 1:
    print("Correct!")
else:
    print("Something wrong!")