from subprocess import Popen, PIPE
import os
from concurrent.futures import ThreadPoolExecutor

from time import time

def time_it(file_path):
    args = ["./target/release/sat-solver", "{}".format(file_path)]
    process = Popen(args, stdout=PIPE, stderr=PIPE)
    (output, err) = process.communicate()
    exit_code = process.wait()
    output = output.decode("utf8")
    if err:
        print(" ".join(args))
        print(err.decode("utf8"))
        raise Exception(file_path)
    sp = output.split('\n')
    solution = sp[0]
    time = float(sp[-2])
    return solution, time

def main(path='wufs/wuf-N', max_workers=4):
    start = time()
    data = {}
    dirs = list(filter(lambda x: x.find('.') == -1, os.listdir(path)))
    executor = ThreadPoolExecutor(max_workers=max_workers)
    futures = []
    for d in dirs:
        instance = data.get(d, {})
        data[d] = instance
        files = os.listdir(os.path.join(path, d))
        for file in files:
            instance[file[:-6]] = res = instance.get(file[:-6],{})
            f = executor.submit(fn, os.path.join(path, d, file), res)
            futures.append(f)
    for f in futures:
        f.result()

    end = time()
    return data, end-start

def process_data(data, path='wufs/wuf-N'):
    res = {}
    for d in data:
        s = ""
        dt = data[d]
        sm = 0
        m = 0
        for i in dt:
            s += i + ' ' + dt[i]['solution'] + '\n'
            time = dt[i]['time']
            sm += time
            m = max(m, time)
        f = open(os.path.join(path, d + '-opt.dat'), 'w')
        f.write(s)
        f.close()
        res[d] = {'avg': sm / len(dt), 'max': m}
    return res




def fn(p, res):
    solution, time = time_it(p)
    res['time'] = time
    res['solution'] = solution