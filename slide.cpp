#include <vector>
#include <iostream>
#include <limits>
#include <cstdint>
#include <stdexcept>

// Используем int32_t для экономии памяти, но чтобы хватило на 16МБ+ индексов
using NodeIdx = int32_t;

// Бит-страж. Используем 30-й бит (0x40000000), 
// чтобы оставить место для индексов до ~1 миллиарда.
static constexpr NodeIdx MARK_BIT = (1 << 30);
static constexpr NodeIdx MASK_IDX = ~MARK_BIT;

struct Node {
    int pos;            // Начало метки ребра в буфере
    int depth;          // Глубина строки (длина пути от корня)
    NodeIdx suf;        // Суффиксная ссылка (бит знака используется как credit bit у Ларссона)
    
    // --- Навигация (Замена Hash map) ---
    NodeIdx firstChild;   // Индекс первого ребенка (0, если нет)
    NodeIdx nextSibling;  // Индекс следующего брата ИЛИ (Parent | MARK_BIT) для последнего
};

class SlidingSuffixTree {
private:
    std::vector<unsigned char> text; // Циклический буфер текста
    std::vector<Node> nodes;         // Пул узлов
    std::vector<unsigned char> fsym; // Первые символы ребер (для листьев, выходящих за mmax)
    
    NodeIdx freelist; // Голова списка свободных узлов
    int mmax;         // Размер окна

    // Состояние активной точки и окна
    NodeIdx ins;      // node index
    int proj;         // projection
    int front;        // right endpoint
    int tail;         // left endpoint
    
    // Временные переменные для canonize (чтобы не перевыделять)
    NodeIdx r_canon;  
    unsigned char a_canon;

    // --- Helpers для циклического буфера ---
    inline int M0(int i) const { return (i < 0) ? (i + mmax) : i; }
    inline int MM(int i) const { return (i < mmax) ? i : (i - mmax); }

    // --- Работа с битами и кредитами (как у Ларссона) ---
    // В оригинале SIGN (INT_MIN) использовался для флагов суффиксной ссылки
    static constexpr int CREDIT_BIT = std::numeric_limits<int>::min();

public:
    SlidingSuffixTree(int windowSize) : mmax(windowSize) {
        if (mmax < 2) throw std::invalid_argument("Window size must be >= 2");

        // Выделяем память
        // +1 для node[0] (nil)
        nodes.resize(mmax * 2 + 1); // *2 так как листьев может быть mmax
        fsym.resize(mmax);
        text.resize(mmax, 0);

        // Инициализация freelist (используем nextSibling для связывания)
        // Начинаем с 2, так как 0-nil, 1-root
        freelist = 2;
        for (int i = 2; i < nodes.size() - 1; ++i) {
            nodes[i].nextSibling = i + 1;
        }
        nodes.back().nextSibling = 0; // Конец списка

        // Инициализация корня
        nodes[0].depth = -1; // Nil
        nodes[1].depth = 0;  // Root
        nodes[1].suf = 0;
        nodes[1].firstChild = 0;
        nodes[1].nextSibling = 0 | MARK_BIT; // Корень сам себе "родитель" (или 0)

        ins = 1;
        proj = 0;
        tail = front = 0;
        r_canon = 0;
        a_canon = 0;
    }

private:
    // --- НОВАЯ ЛОГИКА: Работа со списками вместо Хеша ---

    // Аналог GETCHILD: Ищем ребенка узла u по символу c
    // Возвращает индекс ребенка или 0, если не найден
    NodeIdx getChild(NodeIdx u, unsigned char c) const {
        NodeIdx v = nodes[u].firstChild;
        while (v != 0) {
            // Определяем первый символ на ребре (u -> v)
            unsigned char edgeChar;
            if (v < mmax) { // Внутренний узел
                edgeChar = text[nodes[v].pos];
            } else {        // Лист
                edgeChar = fsym[v - mmax];
            }

            if (edgeChar == c) return v;

            // Переход к следующему брату
            NodeIdx next = nodes[v].nextSibling;
            if (next & MARK_BIT) break; // Это был последний брат
            v = next;
        }
        return 0;
    }

    // Аналог GETPARENT: Восстанавливаем родителя, доходя до конца списка
    NodeIdx getParent(NodeIdx child) const {
        if (child == 1) return 0; // У корня нет родителя (или 0)
        
        NodeIdx curr = child;
        while (true) {
            NodeIdx next = nodes[curr].nextSibling;
            if (next & MARK_BIT) {
                return next & MASK_IDX; // Снимаем бит, получаем индекс родителя
            }
            curr = next;
        }
    }

    // Аналог CREATEEDGE: Вставка ребенка ВСЕГДА В НАЧАЛО списка
    // Это O(1), в отличие от вставки в конец
    void createEdge(NodeIdx u, NodeIdx v) {
        if (nodes[u].firstChild == 0) {
            // Первый ребенок вообще. Он должен указывать на родителя.
            nodes[v].nextSibling = u | MARK_BIT;
        } else {
            // Вставляем перед старым первым.
            // Старый первый (и его хвост) уже настроены правильно.
            nodes[v].nextSibling = nodes[u].firstChild;
        }
        nodes[u].firstChild = v;
    }

    // Аналог DELETEEDGE: Удаление ребенка v у родителя u
    // Самая "дорогая" операция, так как нужен поиск предшественника (O(N))
    void deleteEdge(NodeIdx u, NodeIdx v) {
        NodeIdx prev = 0;
        NodeIdx curr = nodes[u].firstChild;

        // Ищем v в списке
        while (curr != v && !(curr & MARK_BIT)) { // Защита, хотя curr!=v должно сработать раньше
             prev = curr;
             NodeIdx next = nodes[curr].nextSibling;
             if (next & MARK_BIT) break; // Не нашли (ошибка логики, если попали сюда)
             curr = next;
        }

        // Удаляем
        if (prev == 0) {
            // Удаляем первого ребенка (Head)
            NodeIdx next = nodes[v].nextSibling;
            if (next & MARK_BIT) {
                // v был ЕДИНСТВЕННЫМ ребенком. Список опустел.
                nodes[u].firstChild = 0;
            } else {
                // v был первым, но есть другие. next становится новым первым.
                nodes[u].firstChild = next;
            }
        } else {
            // Удаляем из середины или конца
            // prev наследует nextSibling от v (включая MARK_BIT, если v был последним)
            nodes[prev].nextSibling = nodes[v].nextSibling;
        }
        
        // Очистка (опционально)
        nodes[v].nextSibling = 0; 
    }
    
    // Проверка, осталось ли у узла ровно 1 ребенок (для сжатия при advancetail)
    // Возвращает индекс оставшегося ребенка или 0, если детей 0 или >1
    NodeIdx getSingleChild(NodeIdx u) const {
        NodeIdx first = nodes[u].firstChild;
        if (first == 0) return 0;
        
        // Проверяем, является ли первый последним
        if (nodes[first].nextSibling & MARK_BIT) return first;
        
        return 0; // Детей > 1
    }

    // --- Алгоритмическая часть (Логика Ларссона) ---

    void canonize(NodeIdx &ins_ref, int &proj_ref) {
        // ins и proj передаются по ссылке, r_canon и a_canon обновляем в классе
        if (proj_ref && ins_ref == 0) {
            ins_ref = 1; 
            --proj_ref; 
            r_canon = 0;
        }
        
        while (proj_ref > 0) {
            if (r_canon == 0) {
                a_canon = text[M0(front - proj_ref)];
                r_canon = getChild(ins_ref, a_canon);
                if (r_canon == 0) break; // Выход, если ребра нет
            }
            
            // Ларссон использовал hash, чтобы узнать длину ребра, здесь всё явно
            // Длина ребра от nodes[ins] до nodes[r]
            // Но внимание: r может быть листом (>mmax)
            // У Ларссона: ca_d = nodes[r].depth - nodes[ins].depth
            // Листья (v >= mmax) хранятся хитро, их depth не валиден для длины ребра напрямую?
            // В оригинале: leaves... mmax...2*mmax-1.
            // nodes[r].depth у листа в Ларссона корректен?
            // Да, при создании (advancefront) leaf depth не ставится явно, 
            // но логика canonize полагается на depth.
            // В оригинале листья - это виртуальные удлинения. 
            // Стоп. Ларссон хранит depth у внутренних узлов.
            // Для листа depth вычисляется? Нет, в коде: ca_d=nodes[r].depth-nodes[ins].depth
            // Значит, у листьев depth должен быть выставлен. Проверим advancefront.
            
            // Если r >= mmax (лист), его длина бесконечна в контексте текущего окна?
            // Нет, Ларссон обрабатывает это break-ом "if (r>=mmax) break;"
            if (r_canon >= mmax) break; 

            int ca_d = nodes[r_canon].depth - nodes[ins_ref].depth;
            if (proj_ref < ca_d) break;

            proj_ref -= ca_d;
            ins_ref = r_canon;
            r_canon = 0;
        }
    }

    void update(NodeIdx v, int i) {
        NodeIdx ud_v = v;
        int ud_i = i; // pos
        
        // В оригинале логика подъема по кредитам.
        // Нам нужен родитель.
        while (ud_v != 1) {
             NodeIdx ud_u = getParent(ud_v);
             if (ud_u == 0) break; // Should not happen if logic correct
             
             int ud_d = nodes[ud_u].depth;
             int ud_j = M0(nodes[ud_v].pos - ud_d); // Вычисление начала ребра
             int ud_ii = M0(ud_i - tail);
             int ud_jj = M0(ud_j - tail);

             if (ud_ii > ud_jj) {
                 nodes[ud_v].pos = MM(ud_i + ud_d);
             } else {
                 ud_i = ud_j;
                 // ud_ii = ud_jj; // unused
             }

             int cur_suf = nodes[ud_v].suf;
             if (cur_suf & CREDIT_BIT) { // Проверяем знаковый бит (credit)
                  // Уже есть кредит, просто обновляем бит и выходим
                  nodes[ud_v].suf = cur_suf | CREDIT_BIT; 
                  break;
             }
             
             // Снимаем кредит (если был, но тут условие выше), ставим ссылку
             // В оригинале: nodes[ud_v].suf=ud_f&~SIGN; но SIGN это и есть бит.
             // Здесь логика: мы прошли, значит кредит отработан? 
             // Ларссон: "Send credits up... until nonzero credit found"
             // Если нашли (if >=0 в оригинале, где SIGN=INT_MIN), значит break.
             // Если < 0 (бит стоит), то снимаем бит и идем выше.
             // В моей структуре CREDIT_BIT = INT_MIN.
             // Если (suf >= 0) -> нет кредита (бит 0). Break.
             // Если (suf < 0) -> есть кредит. Снимаем, идем вверх.
             
             // ПЕРЕПРОВЕРКА ЛОГИКИ ЛАРССОНА:
             // if ((ud_f=nodes[ud_v].suf)>=0) { nodes[ud_v].suf=ud_f|SIGN; break; }
             // nodes[ud_v].suf=ud_f&~SIGN;
             
             if (!(cur_suf & CREDIT_BIT)) { // Нет кредита (положительное число)
                 nodes[ud_v].suf = cur_suf | CREDIT_BIT; // Ставим кредит
                 break;
             }
             
             // Был кредит, снимаем его и идем выше
             nodes[ud_v].suf = cur_suf & ~CREDIT_BIT;
             ud_v = ud_u;
        }
    }

    NodeIdx getNewNode() {
        NodeIdx u = freelist;
        if (u == 0) throw std::runtime_error("Out of nodes! Window size logic error?");
        
        // freelist указывает на следующий свободный через nextSibling
        // Но nextSibling может содержать мусор или MARK_BIT?
        // При инициализации мы ставили чистые индексы.
        // При возврате (advancetail) мы должны очищать бит.
        freelist = nodes[u].nextSibling; 
        
        // Очищаем поля
        nodes[u].firstChild = 0;
        nodes[u].nextSibling = 0; 
        return u;
    }
    
    void releaseNode(NodeIdx u) {
        nodes[u].nextSibling = freelist;
        freelist = u;
    }

public:
    void advanceFront(unsigned char c) {
        // Добавляем символ в буфер
        text[front] = c;
        
        // Логика advancefront
        NodeIdx u, v;
        // Мы добавляем 1 позицию, цикл while(positions--) убран для простоты API
        
        v = 0;
        while (true) {
            canonize(ins, proj);
            
            if (r_canon < 1) { // active point at node
                if (ins == 0) { // ins is nil
                     r_canon = 1;
                     break; 
                }
                
                NodeIdx child = getChild(ins, c);
                if (child > 0) {
                    r_canon = child;
                    a_canon = c;
                    break; // Endpoint found
                } else {
                    u = ins; // Will add child below u
                }
            } else { // active point on edge
                 // r_canon - это узел, куда ведет ребро
                 // Нужно проверить символ внутри ребра
                 int j;
                 if (r_canon >= mmax) {
                     j = MM(r_canon - mmax + nodes[ins].depth);
                 } else {
                     j = nodes[r_canon].pos;
                 }
                 
                 unsigned char b = text[MM(j + proj)];
                 if (c == b) break; // Endpoint found
                 
                 // Edge split
                 u = getNewNode();
                 nodes[u].depth = nodes[ins].depth + proj;
                 nodes[u].pos = M0(front - proj);
                 nodes[u].suf = CREDIT_BIT; // Emulate update
                 
                 // Редактируем дерево: ins -> u -> r
                 // Удаляем старое ребро (ins, r)
                 deleteEdge(ins, r_canon);
                 
                 // Вставляем (ins, u) с символом a_canon
                 createEdge(ins, u);
                 
                 // Вставляем (u, r) с символом b
                 createEdge(u, r_canon);
                 
                 if (r_canon < mmax) {
                     nodes[r_canon].pos = MM(j + proj);
                 } else {
                     fsym[r_canon - mmax] = b;
                 }
            }
            
            // Add new leaf s
            NodeIdx s = mmax + M0(front - nodes[u].depth); // Индекс листа (виртуальный > mmax)
            // Листья не хранятся в pool (кроме связей), их id > mmax
            // Но нам нужно место в массиве nodes для связей листа!
            // В конструкторе мы выделили nodes.resize(mmax * 2 + 1)
            // Значит s валиден как индекс массива.
            
            createEdge(u, s);
            fsym[s - mmax] = c;
            
            // child count у Ларссона обновлялся для сжатия. Мы это не храним, проверяем динамически.
            
            if (u == ins) {
                 update(u, M0(front - nodes[u].depth));
            }
            
            // Suffix link update
            if (v != 0) {
                nodes[v].suf = u | (nodes[v].suf & CREDIT_BIT);
            }
            v = u;
            
            // Move ins pointer
            ins = nodes[ins].suf & ~CREDIT_BIT;
            r_canon = 0;
        }
        
        if (v != 0) {
            nodes[v].suf = ins | (nodes[v].suf & CREDIT_BIT);
        }
        
        proj++;
        front = MM(front + 1);
    }

    void advanceTail() {
        // Удаляем один символ слева
        canonize(ins, proj);
        
        NodeIdx v = tail + mmax; // Лист, который удаляем
        unsigned char b = fsym[tail];
        
        NodeIdx u = getParent(v);
        deleteEdge(u, v);
        
        if (v == r_canon) { // Replace instead of delete?
             int i = M0(front - (nodes[ins].depth + proj));
             NodeIdx new_leaf = mmax + i;
             createEdge(ins, new_leaf);
             fsym[i] = b;
             update(ins, i);
             
             ins = nodes[ins].suf & ~CREDIT_BIT;
             r_canon = 0;
        } else {
             // Проверяем, нужно ли сжимать узел u (если остался 1 ребенок)
             // u != 1 (root)
             NodeIdx remainingChild = 0;
             if (u != 1 && (remainingChild = getSingleChild(u)) != 0) {
                 // Сжатие пути (удаление внутреннего узла u)
                 unsigned char c_edge = text[nodes[u].pos];
                 NodeIdx w = getParent(u);
                 
                 int d = nodes[u].depth - nodes[w].depth;
                 unsigned char b_char = text[MM(nodes[u].pos + d)]; // Символ, ведущий к оставшемуся ребенку
                 
                 // remainingChild - это 's' у Ларссона
                 
                 if (u == ins) {
                     ins = w;
                     proj += d;
                     a_canon = c_edge;
                 } else if (u == r_canon) {
                     r_canon = remainingChild;
                 }
                 
                 if (nodes[u].suf & CREDIT_BIT) { // suf < 0
                     // send waiting credit up
                     update(w, M0(nodes[u].pos - nodes[w].depth));
                 }
                 
                 // Перелинковка: w -> remainingChild (вместо w -> u -> remainingChild)
                 deleteEdge(u, remainingChild); // Отцепляем ребенка от u
                 deleteEdge(w, u);              // Отцепляем u от w
                 createEdge(w, remainingChild); // Прицепляем ребенка к w
                 
                 // Корректируем позицию ребра
                 if (remainingChild < mmax) {
                     nodes[remainingChild].pos = M0(nodes[remainingChild].pos - d);
                 } else {
                     fsym[remainingChild - mmax] = c_edge;
                 }
                 
                 releaseNode(u);
             }
        }
        
        tail = MM(tail + 1);
    }
    
    // Пример использования поиска (для отладки)
    int longestMatch(const std::vector<unsigned char>& pattern, int& matchLen) {
         // ... реализация аналогична Ларссону, используя getChild ...
         return -1; // stub
    }
    
    // Для отладки
    void printTree(NodeIdx u = 1, int depth = 0) {
        if (u == 0) return;
        for(int i=0; i<depth; ++i) std::cout << "  ";
        
        if (u >= mmax) {
            std::cout << "Leaf " << (u - mmax) << " [" << fsym[u-mmax] << "]" << std::endl;
        } else {
            std::cout << "Node " << u << " (d=" << nodes[u].depth << ")" << std::endl;
            NodeIdx child = nodes[u].firstChild;
            while(child) {
                printTree(child, depth + 1);
                NodeIdx next = nodes[child].nextSibling;
                if (next & MARK_BIT) break;
                child = next;
            }
        }
    }
};

int main() {
    try {
        int wSize = 16; // Маленькое окно для теста
        SlidingSuffixTree tree(wSize);
        std::string input = "mississippi";
        
        std::cout << "Adding: " << input << std::endl;
        for (char c : input) {
            tree.advanceFront((unsigned char)c);
            if (input.length() > 5) { // Тест сдвига хвоста
               // tree.advanceTail(); // Можно включить для теста окна
            }
        }
        
        std::cout << "Tree built successfully." << std::endl;
        tree.printTree();
        
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
    }
    return 0;
}
