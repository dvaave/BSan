#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>

typedef struct {
    unsigned long id;
    unsigned long high;
    unsigned long low;
} Item;

typedef struct {
    Item* items;
    long top;
    unsigned long capacity;
} Stack;

void initialize(Stack* stack, unsigned long capacity) {
    stack->items = (Item*)malloc(capacity * sizeof(Item));
    stack->top = -1;
    stack->capacity = capacity;
}

bool is_empty(Stack* stack) {
    return stack->top == -1;
}

bool is_full(Stack* stack) {
    return stack->top == stack->capacity - 1;
}

void resize(Stack* stack) {
    unsigned long new_capacity = stack->capacity * 2; // Double the capacity (you can choose a different resizing strategy if you prefer)
    Item* new_items = (Item*)realloc(stack->items, new_capacity * sizeof(Item));

    if (new_items == NULL) {
        //printf("Memory allocation error during resizing.\n");
        return;
    }

    stack->items = new_items;
    stack->capacity = new_capacity;
}

unsigned long find_stacktop(Stack* stack, unsigned long id) {
    unsigned long dd = 0xffffffffffff;
    for (long i = stack->top; i >= 0; i--) {
        if (stack->items[i].id == id) {
            return stack->items[i].high;
        }
    }

    //printf("Item with id %lu not found in the stack.\n", id);
    return dd; // Assuming 0 is not a valid address
}

bool find_rspid(Stack* stack, unsigned long id){
    for (long i = stack->top; i >= 0; i--) {
        if (stack->items[i].id == id) {
            return true;
        }
    }
    return false;
}

long find_position(Stack* stack, unsigned long id){
    long kk = -1;
    for (long i = stack->top; i >= 0; i--) {
        if (stack->items[i].id == id) {
            return i;
        }
    }
    return kk;
}

void push(Stack* stack, unsigned long id, unsigned long addr) {
    if (is_full(stack)) {
        resize(stack);
    }

    stack->items[++(stack->top)].id = id;
    stack->items[stack->top].high = addr;
    stack->items[stack->top].low = 0xffffffffffff;
}

void insertlow(Stack* stack, unsigned long id, unsigned long low){
    unsigned long dd = 0xffffffffffff;
    for (long i = stack->top; i >= 0; i--) {
        if (stack->items[i].id == id) {
            stack->items[i].low = low;
        }
    }
}

Item pop(Stack* stack) {
    Item emptyItem = { 0, 0 }; // An empty item to return if the stack is empty

    if (is_empty(stack)) {
        //printf("Stack underflow. Cannot pop from an empty stack.\n");
        return emptyItem;
    }

    return stack->items[(stack->top)--];
}

Item peek(Stack* stack) {
    Item emptyItem = { 0, 0 }; // An empty item to return if the stack is empty

    if (is_empty(stack)) {
        //printf("Stack is empty. Cannot peek into an empty stack.\n");
        return emptyItem;
    }

    return stack->items[stack->top];
}

Item peeksecond(Stack* stack) {
    Item emptyItem = { 0, 0 };
    if(stack->top - 1 == -1){
        //printf("Stack is empty. Cannot peek into an empty stack.\n");
        return emptyItem;
    }else{
        return stack->items[(stack->top)-1];
    }
}

void clear(Stack* stack) {
    free(stack->items);
    stack->items = NULL;
    stack->top = -1;
    stack->capacity = 0;
}

/*int main() {
    unsigned long initialCapacity = 5;
    Stack* stack = (Stack*)malloc(sizeof(Stack));
    initialize(stack, initialCapacity);

    for (int i = 1; i <= 10; i++) {
        push(stack, (unsigned long)i * 10, (unsigned long)i * 100);
    }

    Item topItem = peek(stack);
    printf("Top item: id=%lu, addr=%lu\n", topItem.id, topItem.addr);

    Item poppedItem = pop(stack);
    printf("Popped item: id=%lu, addr=%lu\n", poppedItem.id, poppedItem.addr);

    printf("Top item after pop: id=%lu, addr=%lu\n", peek(stack).id, peek(stack).addr);

    printf("Is the stack empty? %s\n", is_empty(stack) ? "Yes" : "No");

    clear(stack);
    free(stack);

    return 0;
}*/

