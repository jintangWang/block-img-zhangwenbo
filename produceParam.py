import os

filePath = './mp4-result/'

files = os.listdir(filePath)


def customSort(str):
    index = str.find('.')
    # print(str, index, str[5:index])
    return int(index if index == 0 else str[5:index])


files.sort(key=customSort)

with open('paramVideoFrame.txt', 'w') as f:
    for line in files:
        f.write(f"./mp4-result/{line}\n")

# print(files)
