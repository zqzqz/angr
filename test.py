import angr
import sys
import logging
from angr import global_apis
logging.getLogger('angr').setLevel('WARN')

for model in ["paged", "flat", "segmented"]:
    global_apis.MEMORY_MODEL = model

    for i in range(6):
        example = "test{}".format(i+1)
        global_apis.LOAD_COUNT, global_apis.STORE_COUNT, global_apis.CORRECT_LOAD_COUNT = 0, 0, 0

        project = angr.Project("examples/{}/{}".format(example, example), load_options={'auto_load_libs': False})

        state = project.factory.entry_state()
        sm = project.factory.simulation_manager(state)
        sm.run(n=30)

        line = "{},{},{},{},{},{}".format(
            model, example,
            global_apis.STORE_COUNT, 
            global_apis.LOAD_COUNT, 
            global_apis.CORRECT_LOAD_COUNT, 
            global_apis.CORRECT_LOAD_COUNT / global_apis.LOAD_COUNT)
        print(line)
        with open("report.csv", "a") as f:
            f.write(line + "\n")