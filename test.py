import os
import json

def count_files_in_subdirectories(directory):
    subdir_file_count = {}
    for root, dirs, files in os.walk(directory):
        subdir_file_count[root] = len(files)

    return subdir_file_count

directory_to_count = './Result'
subdir_file_counts = count_files_in_subdirectories(directory_to_count)

for subdir, count in subdir_file_counts.items():
    if count!=362 and count!=1:
        print(f'{subdir}: {count} files')