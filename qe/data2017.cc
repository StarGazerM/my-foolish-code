// c style c++ for data structure problem 2017

#include <assert.h>
#include <iostream>
#include <string>
#include <sstream>
#include <utility>
#include <vector>

#define LEAF 0
#define BRANCH 1
#define NODE_T int

namespace rope
{

    class rope
    {
    public:
        int length;      // effective when BRANCH
        std::string str; // effective when leaf
        rope *left;
        rope *right;
        // in c++ a value constructor mean 2 different contructor for LEAF and BRANCH
        rope(std::string s);
        rope(int len, rope *l, rope *r);
        NODE_T type();
        std::string show();
        rope *clone();
        ~rope();

    private:
        int _type; // LEAF or BRANCH
    };

    rope::rope(std::string s)
    {
        this->_type = LEAF;
        this->length = s.size();
        this->left = nullptr;
        this->right = nullptr;
        this->str = s;
    }

    rope::rope(int len, rope *left, rope *right)
    {
        this->_type = BRANCH;
        this->length = len;
        this->left = left;
        this->right = right;
        this->str = "";
    }

    rope::~rope()
    {
        if (left != nullptr)
        {
            delete left;
        }
        if (right != nullptr)
        {
            delete right;
        }
    }

    NODE_T rope::type()
    {
        return this->_type;
    }

    std::string rope::show()
    {
        if (this->type() == LEAF)
        {
            return this->str;
        }
        if (this->type() == BRANCH)
        {
            // assert(length == this->left->length + this->right->length);
            return this->left->show() + this->right->show();
        }
        else
        {
            return "";
        }
    }

    // return a clone of a rope itself
    rope *rope::clone()
    {
        rope *new_rope = nullptr;
        if (type() == LEAF)
        {
            new_rope = new rope(this->str);
        }
        else
        {
            new_rope = new rope(this->length, this->left->clone(), this->right->clone());
        }
        return new_rope;
    }

    rope *concat(rope *r1, rope *r2)
    {
        rope *new_rope = nullptr;
        // match the type first
        if (r1->type() == LEAF && r2->type() == LEAF)
        {
            int new_len = r1->str.size() + r2->str.size();
            new_rope = new rope(new_len, r1->clone(), r2->clone());
        }
        else if (r1->type() == LEAF && r2->type() == BRANCH)
        {
            int new_len = r1->str.size() + r2->length;
            new_rope = new rope(new_len, r1->clone(), r2->clone());
        }
        else if (r1->type() == BRANCH && r2->type() == LEAF)
        {
            int new_len = r1->length + r2->str.size();
            new_rope = new rope(new_len, r1->clone(), r2->clone());
        }
        else if (r1->type() == BRANCH && r2->type() == BRANCH)
        {
            int new_len = r1->length + r2->length;
            new_rope = new rope(new_len, r1->clone(), r2->clone());
        }
        assert(new_rope != nullptr);
        return new_rope;
    }

    // assume no out of bound
    char index(rope *r, int pos)
    {
        if (r->type() == LEAF)
        {
            return r->str[pos];
        }
        if (r->type() == BRANCH)
        {
            if (pos < r->left->length)
            {
                return index(r->left, pos);
            }
            else
            {
                return index(r->right, pos - r->left->length);
            }
        }
    }

    std::pair<rope *, rope *> split(rope *r, int pos)
    {
        if (r->type() == LEAF)
        {
            rope *r1 = new rope(r->str.substr(0, pos));
            rope *r2 = new rope(r->str.substr(pos, r->str.size()));
            return std::make_pair(r1, r2);
        }
        if (r->type() == BRANCH)
        {
            if (pos < r->left->length)
            {
                std::pair<rope *, rope *> splited_left = split(r->left, pos);
                rope *r1 = splited_left.first;
                rope *r2 = r->clone();
                rope *tmp = r2->left;
                r2->left = splited_left.second;
                r2->length = r2->length - pos;
                delete tmp;
                return std::make_pair(r1, r2);
            }
            else if (pos == r->left->length)
            {
                return std::make_pair(r->left->clone(), r->right->clone());
            }
            else
            {
                std::pair<rope *, rope *> splited_right = split(r->right, pos - r->left->length);
                rope *r2 = splited_right.second;
                rope *r1 = r->clone();
                rope *tmp = r1->right;
                r1->right = splited_right.first;
                delete tmp;
                return std::make_pair(r1, r2);
            }
        }
    }

    rope *insert(rope *r, std::string s, int pos)
    {
        std::pair<rope *, rope *> splited_r = split(r, pos);
        rope *new_leaf = new rope(s);
        rope *new_right = concat(splited_r.first, new_leaf);
        rope *p = concat(new_right, splited_r.second);
        // clean
        delete splited_r.first;
        delete splited_r.second;
        delete new_leaf;
        delete new_right;
        return p;
    }

    rope *del(rope *r, int from, int to)
    {
        std::pair<rope *, rope *> splited_r = split(r, from);
        rope *new_left = splited_r.first;
        std::pair<rope *, rope *> splited_rr = split(splited_r.second, to-1);
        rope *res = concat(new_left, splited_rr.second);
        // clean
        delete splited_r.first;
        delete splited_r.second;
        delete splited_rr.first;
        delete splited_rr.second;
        return res;
    }
}

int main()
{
    // generate a lot of leaf
    rope::rope *l1 = new rope::rope("hello_");
    rope::rope *l2 = new rope::rope("my_");
    rope::rope *l3 = new rope::rope("na");
    rope::rope *l4 = new rope::rope("me_i");
    rope::rope *l5 = new rope::rope("s");
    rope::rope *l6 = new rope::rope("_simon");
    rope::rope *c1 = rope::concat(l1, l2);
    rope::rope *c2 = rope::concat(l3, l4);
    rope::rope *c3 = rope::concat(l5, l6);
    rope::rope *d1 = rope::concat(c2, c3);
    rope::rope *test = rope::concat(c1, d1);
    std::cout << test->show().c_str() << std::endl;
    char tc =  rope::index(test, 14);
    std::cout << tc << std::endl;
    auto splited = rope::split(test, 13);
    std::cout << splited.first->show() << "  |  " << splited.second->show() << std::endl;
    auto inserted = rope::insert(test, "ww", 13);
    std::cout << inserted->show() << std::endl;
    auto deleted = rope::del(inserted, 13, 15);
    std::cout << deleted->show() << std::endl;
    return 0;
}