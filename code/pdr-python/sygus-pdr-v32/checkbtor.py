from btorparser import BTOR2Parser
from pdr import PDR

import argparse
from pathlib import Path

def check(btorfname): # will need to dump inv/result to file
    btor_parser = BTOR2Parser()
    sts, _ = btor_parser.parse_file(Path(btorfname))
    pdr_checker = PDR(sts)
    if not pdr_checker.check_property(sts.assertion):
        print ('FAIL!')
        return

    pdr_checker.sanity_check_imply()
    pdr_checker.sanity_check_frame_monotone()
    pdr_checker.sanity_check_safe_inductive_inv(sts.assertion)
    pdr_checker.dump_frames()
    print ('SUCCEED: ', pdr_checker.get_inv_str())

def main():
    parser = argparse.ArgumentParser(description='PDR on btor2')
    parser.add_argument('file', help='btor2 input')
    args = parser.parse_args()
    check(args.file)

if __name__ == '__main__':
    main()