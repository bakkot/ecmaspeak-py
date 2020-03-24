#!/usr/bin/python3

# compare_and_replace.py [-d dir_prefix] path ...
# Compare old and new versions of designated files/directories;
# at user option, replace old with new.
#
# Copyright (C)  J. Michael Dyck <jmdyck@ibiblio.org>

import sys, os, stat, filecmp, shutil, fnmatch
from collections import defaultdict
# import misc

def main():
    argv = sys.argv
    executable = argv.pop(0)
    if argv[0] == '-d':
        argv.pop(0)
        common_dir_prefix = argv.pop(0)
    else:
        common_dir_prefix = None

    for arg in argv:
        if common_dir_prefix:
            path = common_dir_prefix + '/' + arg
        else:
            path = arg

        if path.endswith('.new'):
            new_path = path
            cur_path = new_path[:-4]
        else:
            cur_path = path
            new_path = cur_path + '.new'

        if not os.path.exists(new_path):
            stderr(f'ERROR: new_path does not exist: {new_path}')
            # Do you want to delete old_path?
            continue

        if not os.path.exists(cur_path):
            stderr(f'{cur_path} does not exist, so installing {new_path} there')
            os.rename(new_path, cur_path)
            continue

        # At this point, we know that both things exist.

        cur_type = get_type(cur_path)
        if cur_type == 'other':
            stderr(f'ERROR: {cur_path} is neither a regular file nor a directory.')
            continue

        new_type = get_type(new_path)
        if new_type == 'other':
            stderr(f'ERROR: {new_path} is neither a regular file nor a directory.')
            continue

        if cur_type != new_type:
            stderr(f'ERROR: {cur_path} is a {cur_type}, but {new_path} is a {new_type}')
            continue

        # At this point, we know they have the same type.

        if cur_type == 'reg':
            handle_files(cur_path, new_path)
        elif cur_type == 'dir':
            handle_dirs(cur_path, new_path)
        else:
            assert 0, cur_type

def get_type(path):
    stat_result = os.lstat(path)
    if stat.S_ISDIR(stat_result.st_mode):
        return 'dir'
    elif stat.S_ISREG(stat_result.st_mode):
        return 'reg'
    else:
        return 'other'

def handle_files(cur_path, new_path):
    if filecmp.cmp(cur_path, new_path, shallow=False):
        # same content
        stderr(f'No change from {cur_path}')
        os.remove(new_path)
    else:
        # different content
        gdiff(cur_path, new_path)
        response = get_input(f"update {cur_path} ?", ['y', 'n', 'q'])
        if response == 'y':
            os.rename(new_path, cur_path)
        elif response == 'n':
            stderr('(not overwriting)')
        elif response == 'q':
            sys.exit(1)
        else:
            assert 0

def handle_dirs(cur_root, new_root):
    action_for_item_ = {}

    def recurse_on_rel_path(dir_rel_path):
        # print('>', dir_rel_path)

        d = defaultdict(lambda: [None, None])
        roots = [cur_root, new_root]
        for (i, root) in enumerate(roots):
            path = root + '/' + dir_rel_path
            for entry in os.scandir(path):
                if fnmatch.fnmatchcase(entry.name, '.*.swp'):
                    stderr(f"ignoring: {path}/{entry.name}")
                    continue
                d[entry.name][i] = entry

        for (item_name, (c_entry, n_entry)) in sorted(d.items()):
            item_rel_path = dir_rel_path + '/' + item_name
            # print(item_name, c_entry, n_entry)
            if c_entry is None and n_entry is None:
                assert 0 # can't happen
            elif n_entry is None:
                action = ('delete', c_entry)
            elif c_entry is None:
                action = ('create', n_entry)
            else:
                # alter or leave...
                if c_entry.is_file(follow_symlinks=False) and n_entry.is_file(follow_symlinks=False):
                    # both files
                    if filecmp.cmp(c_entry.path, n_entry.path, shallow=False):
                        # same content
                        action = ('leave', c_entry, n_entry)
                    else:
                        # different
                        action = ('alter', c_entry, n_entry)
                elif c_entry.is_dir() and n_entry.is_dir():
                    # both dirs
                    recurse_on_rel_path(item_rel_path)
                    action = None
                else:
                    # change of type!
                    assert 0, (c_entry, n_entry)

            if action is not None:
                # print(item_rel_path, action[0])
                action_for_item_[item_rel_path] = action

    recurse_on_rel_path('.')

    would_ = {
        'delete': [],
        'create': [],
        'alter': [],
        'leave': [],
    }
    for (item_rel_path, action) in sorted(action_for_item_.items()):
        would_[action[0]].append(item_rel_path)

    print()
    print(f'Replacing {cur_root} with {new_root} would...')
    if all(len(would_[verb]) == 0 for verb in ['delete','create','alter']):
        print(f'    have no effect,')
        print(f'    so removing {new_root}...')
        shutil.rmtree(new_root)
        return

    for (verb, item_rel_paths) in would_.items():
        print()
        print(f'    {verb}:')
        if item_rel_paths == []:
            print('        (nothing)')
        else:
            if verb == 'leave' and len(item_rel_paths) > 10:
                print(f'        ({len(item_rel_paths)} items)')
            else:
                for item_path in item_rel_paths:
                    print(f'        {item_path.replace("./", "")}')

    while True:
        stderr()
        response = get_input("select a group to examine [dcal] or 'y' to install the new or 'n' to skip it:", 'd c a l y n'.split())
        if response == 'y':
            stderr(f"installing {new_root}...")
            shutil.rmtree(cur_root)
            os.rename(new_root, cur_root)
            return
        elif response == 'n':
            stderr(f"skipping {new_root}...")
            return
        else:
            verb = {
                'd': 'delete',
                'c': 'create',
                'a': 'alter',
                'l': 'leave',
            }[response]
            for item_rel_path in would_[verb]:
                c_path = cur_root + '/' + item_rel_path
                n_path = new_root + '/' + item_rel_path
                gdiff(c_path, n_path)

    #            if verb == 'delete':
    #                gdiff(c_path, '/dev/null')
    #            elif verb == 'create':
    #                gdiff('/dev/null', n_path)
    #            elif verb == 'alter':
    #                gdiff(c_path, n_path)
    #            elif verb == 'leave':
    #                gdiff(c_path, n_path)
    #            else:
    #                assert 0

def gdiff(L_path, R_path):
    retcode = os.system(f"gdiff -f -R -c 'windo set nonu| syntax off' '{L_path}' '{R_path}'")
    # -f: foreground
    # -R: readonly
    # -c ...:  "execute command after loading the first file"
    if retcode != 0: stderr("return code was {retcode}")

def get_input(prompt, valid_responses):
    while True:
        response = input(f'{prompt} ')
        if response in valid_responses:
            return response
        else:
            stderr(f"You responded '{response}'")

def stderr(*args):
    print(*args, file=sys.stderr)

main()

# vim: sw=4 ts=4 expandtab