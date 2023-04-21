"""
TODO: Finish the auto download..
  NOTE: all files are ignored in efmc/solvers except this one (download.py)
  (Currently, better to download, cp, rename, and chmod manually)
"""

import platform
import os
import sys

cvc5_mac_arm64 = "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.3/cvc5-macOS-arm64"
cvc5_mac = "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.3/cvc5-macOS"
cvc5_win64 = "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.3/cvc5-Win64.exe"
cvc5_linux = "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.3/cvc5-Linux"

z3_mac_arm64 = "https://github.com/Z3Prover/z3/releases/download/z3-4.10.2/z3-4.10.2-arm64-osx-11.0.zip"
z3_mac = "https://github.com/Z3Prover/z3/releases/download/z3-4.10.2/z3-4.10.2-x64-osx-10.16.zip"
z3_win64 = "https://github.com/Z3Prover/z3/releases/download/z3-4.10.2/z3-4.10.2-x64-win.zip"
z3_linux = "https://github.com/Z3Prover/z3/releases/download/z3-4.10.2/z3-4.10.2-x64-glibc-2.31.zip"

mathsat5_mac = "https://mathsat.fbk.eu/download.php?file=mathsat-5.6.9-osx.tar.gz"
mathsat5_win64 = "https://mathsat.fbk.eu/download.php?file=mathsat-5.6.9-win64-msvc.zip"
mathsat5_linux = "https://mathsat.fbk.eu/download.php?file=mathsat-5.6.9-linux-x86_64.tar.gz"

yices2_mac_arm64 = "https://github.com/SRI-CSL/yices2/releases/download/Yices-2.6.4/yices-2.6.4-arm-apple-darwin20.6.0.tar.gz"
yices2_mac = "https://github.com/SRI-CSL/yices2/releases/download/Yices-2.6.4/yices-2.6.4-x86_64-apple-darwin20.6.0.tar.gz"
yices2_win64 = "https://github.com/SRI-CSL/yices2/releases/download/Yices-2.6.4/yices-2.6.4-x86_64-unknown-mingw32-static-gmp.zip"
yices2_linux = "https://github.com/SRI-CSL/yices2/releases/download/Yices-2.6.4/yices-2.6.4-x86_64-pc-linux-gnu.tar.gz"


mac_arm_targets = [cvc5_mac_arm64, z3_mac_arm64, mathsat5_mac , yices2_mac_arm64]
mac_targets = [cvc5_mac, z3_mac, mathsat5_mac , yices2_mac]
linux_targets = [cvc5_linux, z3_linux, mathsat5_linux , yices2_linux]


def get_os_type():
    name = platform.platform()
    print(name)
    if name.startswith("mac"):
        return "mac"
    elif name.startswith("Linux"):
        return "linux"
    else:
        return "error"


def download_targets(tool_urls):
    for url in tool_urls:
        cmd = "wget " + url
        os.system(cmd)
        print("Finish downloading " + url)


def check_success():
    return


if __name__ == '__main__':
    os_name = get_os_type()
    if os_name == "mac":
        download_targets(mac_targets)
    elif os_name == "linux":
        download_targets(linux_targets)
    else:
        print("only support mac and linux")

