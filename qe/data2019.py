from dataclasses import dataclass

@dataclass
class CTrie:
    color: str
    val: str
    child: [any]

t1 = CTrie(
    color='grey',
    val='',
    child=[
        CTrie(
            color='black', 
            val='a', 
            child=[CTrie(color='black', val='t', child=[CTrie(color='black', val='e', child=[])])]),
        CTrie(
            color='grey',
            val='o',
            child=[
                CTrie(color='black', val='n', child=[CTrie(color='black', val='e', child=[])]),
                CTrie(color='grey', val='u', child=[CTrie(color='black', val='t', child=[])])
            ]
        )
    ]
)

def search(s:str , ct: CTrie) -> bool:
    ''' search a string in a ctrie '''
    if ct.val == '':
        res = False
        for c in ct.child:
            res = res or search(s, c)
        return res
    if s == '':
        return True
    head = s[0]
    tail = s[1:]
    if ct.val == head:
        if ct.color == 'grey':
            if tail == '':
                return False
            child_res = False
            for c in ct.child:
                child_res = child_res or search(tail, c)
            return child_res
        if ct.color == 'black':
            child_res = False
            if ct.child == []:
                child_res = True
            for c in ct.child:
                child_res = child_res or search(tail, c)
            return child_res
    else:
        return False

print(search('out', t1))