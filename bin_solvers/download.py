"""
Download Z3, CVC5, and Eldarica solvers
"""

import os
import platform
import re
import shutil
import sys
import tarfile
import zipfile

import requests
from tqdm import tqdm

SOLVER_URLS = {
    'mac_arm64': {
        'cvc5': "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.3/cvc5-macOS-arm64",
        'z3': "https://github.com/Z3Prover/z3/releases/download/z3-4.10.2/z3-4.10.2-arm64-osx-11.0.zip",
        "eldarica": "https://github.com/uuverifiers/eldarica/releases/download/v2.2/eldarica-bin-2.2.zip"
    },
    'mac_x64': {
        'cvc5': "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.3/cvc5-macOS",
        'z3': "https://github.com/Z3Prover/z3/releases/download/z3-4.10.2/z3-4.10.2-x64-osx-10.16.zip",
        "eldarica": "https://github.com/uuverifiers/eldarica/releases/download/v2.2/eldarica-bin-2.2.zip"
    },
    'linux': {
        'cvc5': "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.3/cvc5-Linux",
        'z3': "https://github.com/Z3Prover/z3/releases/download/z3-4.10.2/z3-4.10.2-x64-glibc-2.31.zip",
        "eldarica": "https://github.com/uuverifiers/eldarica/releases/download/v2.2/eldarica-bin-2.2.zip"
    }
}

def get_z3_path(name):
    # Extract directory name by removing .zip extension
    if name.endswith('.zip'):
        dir_name = name[:-4]  # Remove .zip
        return f'{dir_name}/bin/z3'
    return None

BINARY_PATHS = {
    'cvc5': lambda name: name,
    'z3': get_z3_path,
    'eldarica': lambda name: 'eldarica-2.2/eld'
}


def get_os_type():
    system = platform.system().lower()
    if system == 'darwin':
        return 'mac_arm64' if platform.machine() == 'arm64' else 'mac_x64'
    return 'linux' if system == 'linux' else None


def download_file(url):
    filename = url.split('/')[-1]
    try:
        response = requests.get(url, stream=True)
        total_size = int(response.headers.get('content-length', 0))
        
        with open(filename, 'wb') as file, tqdm(
                desc=f"Downloading {filename}",
                total=total_size,
                unit='iB',
                unit_scale=True,
                unit_divisor=1024,
        ) as pbar:
            for data in response.iter_content(chunk_size=1024):
                pbar.update(file.write(data))
        return filename
    except Exception as e:
        print(f"Failed to download {url}: {e}")
        return None


def extract_archive(filename):
    try:
        if filename.endswith('.zip'):
            with zipfile.ZipFile(filename, 'r') as zip_ref:
                zip_ref.extractall()
        elif filename.endswith('.tar.gz'):
            with tarfile.open(filename, 'r:gz') as tar_ref:
                tar_ref.extractall()
        return True
    except Exception as e:
        print(f"Failed to extract {filename}: {e}")
        return False


def setup_solver(solver_name, url, bin_dir):
    """Setup a single solver"""
    target_path = os.path.join(bin_dir, solver_name)
    
    # Skip if already exists
    if os.path.exists(target_path):
        print(f"✓ {solver_name} already exists, skipping")
        return True
    
    print(f"Setting up {solver_name}...")
    
    # Download
    downloaded_file = download_file(url)
    if not downloaded_file:
        return False
    
    # Extract if needed
    if downloaded_file.endswith(('.zip', '.tar.gz')):
        if not extract_archive(downloaded_file):
            return False
        binary_path = BINARY_PATHS[solver_name](downloaded_file)
    else:
        binary_path = downloaded_file
    
    # Copy binary
    if binary_path and os.path.exists(binary_path):
        if solver_name == 'eldarica':
            # For Eldarica, copy the entire directory since it's a bash script with dependencies
            eldarica_dir = os.path.join(bin_dir, 'eldarica-2.2')
            if os.path.exists(eldarica_dir):
                shutil.rmtree(eldarica_dir)
            shutil.copytree('eldarica-2.2', eldarica_dir)
            # Set execute permissions on the actual eld script
            eld_script = os.path.join(eldarica_dir, 'eld')
            os.chmod(eld_script, 0o755)
            # Create a symlink to the actual eld script for easier access
            if os.path.exists(target_path):
                os.remove(target_path)
            os.symlink(eld_script, target_path)
        else:
            shutil.copy2(binary_path, target_path)
            os.chmod(target_path, 0o755)
        
        print(f"✓ {solver_name} setup successful")
        
        # Cleanup
        os.remove(downloaded_file)
        if downloaded_file.endswith(('.zip', '.tar.gz')):
            # Remove extracted directory, but keep eldarica directory
            for item in os.listdir('.'):
                if os.path.isdir(item) and item.startswith('z3-'):
                    shutil.rmtree(item)
                elif os.path.isdir(item) and item.startswith('eldarica-') and solver_name != 'eldarica':
                    shutil.rmtree(item)
        return True
    else:
        print(f"✗ Could not find binary for {solver_name}")
        return False


def setup_solvers():
    os_type = get_os_type()
    if not os_type or os_type not in SOLVER_URLS:
        print(f"Unsupported OS: {platform.system()}")
        return False
    
    bin_dir = os.path.join(os.path.dirname(__file__), 'bin')
    os.makedirs(bin_dir, exist_ok=True)
    
    print(f"Detected OS: {os_type}")
    print(f"Setting up solvers in {bin_dir}")
    
    success = True
    for solver_name, url in SOLVER_URLS[os_type].items():
        if not setup_solver(solver_name, url, bin_dir):
            success = False
    
    return success


if __name__ == '__main__':
    try:
        if setup_solvers():
            print("\n✓ All solvers setup complete")
        else:
            print("\n✗ Some errors occurred")
    except KeyboardInterrupt:
        print("\nSetup interrupted")
        sys.exit(1)
    except Exception as e:
        print(f"\nError: {e}")
        sys.exit(1)
