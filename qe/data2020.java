// java version of data structure 2020

import java.util.ArrayList;

class PQDT {
    private ArrayList<Integer> _data;

    public PQDT() {
        _data = new ArrayList<>();
    }

    private int getParent(int n) {
        return (n - 1) / 2; 
    }

    private int getLeft(int n) {
        int res = n * 2 + 1;
        if (res < _data.size()) {
            return res;
        } else {
            return -1;
        }
    }

    private int getRight(int n) {
        int res = n * 2 + 2;
        if (res < _data.size()) {
            return res;
        } else {
            return -1;
        }
    }

    private void _heapifyParent(int n) {
        if (n == 0) { return; }
        int parent_id = this.getParent(n);
        if (_data.get(n) <= _data.get(parent_id)) {
            // swap
            int tmp = _data.get(n);
            _data.set(n, _data.get(parent_id));
            _data.set(parent_id, tmp);
        }
        _heapifyParent(parent_id);
    }

    private void _rm_min(int n) {
        int left = getLeft(n);
        int right = getRight(n);
        if (left == -1) {
            _data.set(n, _data.get(_data.size() - 1));
            // _data.remove(_data.size() - 1);
        } else if (right == -1) {
            int tmp = _data.get(left);
            _data.set(left, _data.get(_data.size() - 1));
            _data.set(_data.size() - 1, tmp);
            _heapifyParent(left);
            
        } else if (_data.get(left) <= _data.get(right)) {
            _data.set(n, _data.get(left));
            _rm_min(left);
        } else {
            _data.set(n, _data.get(right));
            _rm_min(right);
        }
    }

    public void insert(int n) {
        if (_data.isEmpty()) {
            _data.add(n);
        } else {
            _data.add(n);
            _heapifyParent(_data.size() - 1);
        }
    }

    public int find_min() {
        return _data.get(0);
    }

    public int remove_min() {
        int _min = find_min();
        _rm_min(0);
        _data.remove(_data.size() - 1);
        return _min;
    }
}

class Main {
    public static void main(String[] args) {
        var h = new PQDT();
        h.insert(2);
        h.insert(7);
        h.insert(8);
        h.insert(5);
        h.insert(1);
        h.insert(3);

        System.out.println(h.remove_min());
        System.out.println(h.remove_min());
        System.out.println(h.remove_min());

    }
}