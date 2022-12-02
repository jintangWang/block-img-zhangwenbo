import pypbc

n = 9000
m = 0
filename = []


def get_param():
    fp = open("param100.txt", "r")
    m = fp.readline()
    l = fp.readline()
    for i in range(0, int(m)):
        filename.append(fp.readline())
    id = fp.readline()
    seller = fp.readline()
    buyer = fp.readline()
    times = fp.readline()
    fp.close()
    print(m, l, len(filename), id, seller, buyer, times)


def init():
    N = n + m
    # 初始化配对
    par = Parameters(160)
    print(par)

get_param()
# t0 = time.clock()
print("init...")
init()