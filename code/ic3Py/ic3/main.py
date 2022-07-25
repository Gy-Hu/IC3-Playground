import argparse
import os
from datetime import datetime
from multiprocessing import Process

import ic3.model
import ic3.pdr


test_file_path = "./aag"


def run_with_limited_time(func, time):
    p = Process(target=func)
    p.start()
    p.join(time)
    if p.is_alive():
        p.terminate()
        return False
    return True


if __name__ == '__main__':
    help_info = "Usage: python main.py <file-name>.aag"
    parser = argparse.ArgumentParser(description="Run tests examples on the PDR algorithm")
    parser.add_argument('fileName', type=str, help='The name of the test to run', default=None, nargs='?')
    parser.add_argument('-m', type=int, help='the time limitation of one test to run', default=None)
    parser.add_argument('-c', help='switch to counting time', action='store_true')
    args = parser.parse_args()
    if args.fileName is not None:
        file = args.fileName
        m = ic3.model.Model()
        print("============= Running test ===========")
        solver = ic3.pdr.PDR(*m.parse(file))
        startTime = datetime.now()
        solver.run()
        endTime = datetime.now()
        if args.c:
            print("TIME CONSUMING: " + str((endTime - startTime).seconds) + "seconds")

    else:
        print("================ Test the ./aag directory ========")
        for root, dirs, files in os.walk(test_file_path):
            for name in files:
                print("============ Testing " + str(name) + " ==========")
                m = ic3.model.Model()
                solver = ic3.pdr.PDR(*m.parse(os.path.join(root, name)))

                if not run_with_limited_time(solver.run, args.m):
                    print("Time Out")
                else:
                    print("Done in time")
