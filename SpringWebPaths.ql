/**
 * @name Spring Web Paths Collector
 * @description 检测 Spring MVC/WebFlux 中所有请求路径（包括类和方法级别组合路径）
 * @kind path-problem
 * @id java/spring/web-paths
 */
import java
import semmle.code.java.frameworks.spring.SpringController

// 1. 检测 Controller 类（类级别路径）
predicate isSpringController(Class c) {
  exists(Annotation a | 
    a = c.getAnAnnotation() and
    (
      a.getType().hasQualifiedName("org.springframework.stereotype", "Controller") or
      a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RestController")
    )
  )
}

// 2. 检测请求映射方法（方法级别路径）
predicate isSpringRequestMappingMethod(Method m) {
  exists(Annotation a | 
    a = m.getAnAnnotation() and
    (
      a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestMapping") or
      a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "GetMapping") or
      a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "PostMapping") or
      a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "PutMapping") or
      a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "DeleteMapping") or
      a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "PatchMapping")
    )
  )
}

// 1. 获取类级别路径
string getSpringControllerPath(Class c) {
    exists(Annotation a | 
      a = c.getAnAnnotation() and
      a.getType().hasQualifiedName(
        "org.springframework.web.bind.annotation", "RequestMapping") and
      result = a.getValue("value").toString()
    ) 
    //or
    //result = "" // 默认空路径
  }
  
  // 2. 获取方法级别路径
  string getSpringMethodPath(Method m) {
    exists(Annotation a | 
      a = m.getAnAnnotation() and (
        a.getType().hasQualifiedName(
          "org.springframework.web.bind.annotation", "RequestMapping") or
        a.getType().hasQualifiedName(
          "org.springframework.web.bind.annotation", "GetMapping") or
        a.getType().hasQualifiedName(
          "org.springframework.web.bind.annotation", "PostMapping")
      ) and
      result = a.getValue("value").toString()
    )
  }
  
  // 3. 获取HTTP方法类型
  string getHttpMethod(Method m) {
    exists(Annotation a | 
      a = m.getAnAnnotation() and (
        a.getType().getName() = "GetMapping" and result = "GET" or
        a.getType().getName() = "PostMapping" and result = "POST"
      )
    ) 
    //or
    //result = "ANY" // 默认匹配所有方法
  }
  


  predicate getHttpMethods(Method m) {
    exists(Annotation a |
      a = m.getAnAnnotation() and (
        a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "GetMapping") or
        a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "PostMapping") or
        a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "PutMapping") or
        a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "DeleteMapping") or
        a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "PatchMapping") or
        a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestMapping")
      )
    )
  }

  
  string getHttpMethod1111(Method m) {
    exists(Annotation a |
      a = m.getAnAnnotation() and
      (
        (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "GetMapping") and result = "GET") or
        (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "PostMapping") and result = "POST") or
        (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "PutMapping") and result = "PUT") or
        (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "DeleteMapping") and result = "DELETE") or
        (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "PatchMapping") and result = "PATCH") or
        (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestMapping") and 
          exists(string method | 
            method = a.getValue("method").toString().toUpperCase() and
            result = method
          )
        )
      )
    )
  }
  


  string analyzePathParam(Parameter p) {
    exists(Annotation pathVar |
      pathVar = p.getAnAnnotation()|
      result = pathVar.getType().toString())
  }


  string analyzePathParam_change(Parameter p) {
    exists(Annotation a |
      // Spring MVC 注解检测
      (a = p.getAnAnnotation() and
       (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestParam") and 
        result = "QUERY_PARAM") or
        //test
        (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestHeader") and 
        result = "RequestHeader_PARAM") or
        (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "CookieValue") and 
        result = "CookieValue_PARAM") or
        (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestPart") and 
        result = "multipart/form-data_PARAM") or
        //test
       (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "PathVariable") and 
        result = "PATH_VARIABLE") or
       (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestBody") and 
       result = "BODY")) or
      // JAX-RS 注解检测
      (a.getType().hasQualifiedName("javax.ws.rs", "QueryParam") and 
      result = "QUERY_PARAM") or
      (a.getType().hasQualifiedName("javax.ws.rs", "PathParam") and 
      result = "PATH_VARIABLE")
    )
  }


  string analyzePathParam_change1(Parameter p) {
    // 先检查是否存在任何注解
    if not exists(Annotation a | a = p.getAnAnnotation()) 
    then  result = "不存在注解"
    else 
      exists(Annotation a |
        // Spring MVC 注解检测
        (a = p.getAnAnnotation() and not (
          // 排除校验类注解
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "NotNull") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "NotEmpty") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Size") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Pattern") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Min") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Max") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Valid")
          
          )
        and
         (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestParam") and 
          result = "QUERY_PARAM") or
         (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestHeader") and 
          result = "RequestHeader_PARAM") or
         (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "CookieValue") and 
          result = "CookieValue_PARAM") or
         (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestPart") and 
          result = "multipart/form-data_PARAM") or
         (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "PathVariable") and 
          result = "PATH_VARIABLE") or
         (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestBody") and 
         result = "BODY")) or
        // JAX-RS 注解检测
        (a.getType().hasQualifiedName("javax.ws.rs", "QueryParam") and 
        result = "QUERY_PARAM") or
        (a.getType().hasQualifiedName("javax.ws.rs", "PathParam") and 
        result = "PATH_VARIABLE")   
      )
  }
  


  string analyzePathParam_change2(Parameter p) {
    // 先检查是否存在任何注解
    if not exists(Annotation a | a = p.getAnAnnotation()) 
    then
      result = "不存在注解"
    else 
      exists(Annotation a |
        (a = p.getAnAnnotation() and not (
          // 排除校验类注解
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "NotNull") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "NotEmpty") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Size") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Pattern") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Min") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Max") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Valid") 
          )
        and (
          // Spring MVC 注解检测
          (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestParam") and 
           result = "QUERY_PARAM") or
          (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestHeader") and 
           result = "RequestHeader_PARAM") or
          (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "CookieValue") and 
           result = "CookieValue_PARAM") or
          (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestPart") and 
           result = "multipart/form-data_PARAM") or
          (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "PathVariable") and 
           result = "PATH_VARIABLE") or
          (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestBody") and 
           result = "BODY") or
          // JAX-RS 注解检测
          (a.getType().hasQualifiedName("javax.ws.rs", "QueryParam") and 
           result = "QUERY_PARAM") or
          (a.getType().hasQualifiedName("javax.ws.rs", "PathParam") and 
           result = "PATH_VARIABLE")
        ))
      ) or
      // 存在注解但未匹配任何已知类型
      (result = "未识别注解" and 
       not exists(Annotation a | a = p.getAnAnnotation() and
         a.getType().hasQualifiedName(_, _) and
         result != "未识别注解"))
  }
  



string getFullWebPath(Class c, Method m) {
    exists(string classPath, string methodPath |
      classPath = getSpringControllerPath(c).replaceAll("/+$", "") and
      methodPath = getSpringMethodPath(m) and
      result = (classPath.replaceAll("\"","") + "/" +methodPath.replaceAll("\"","")).replaceAll("//", "/")
    )
  }



// 定义基础类型判断
predicate isBasicType(Type t) {
  t instanceof PrimitiveType or
  t instanceof BoxedType or
  t.hasName("String") or
  t.hasName("LocalDate") or
  t.hasName("LocalDateTime") or
  t.hasName("BigDecimal") or
  t.hasName("BigInteger") or
  t.hasName("Date")
}



string analyzePathParam_change_a(Annotation a) {
      a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestParam") and 
      result = "QUERY_PARAM" or
      //test
      (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestHeader") and 
      result = "RequestHeader_PARAM") or
      (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "CookieValue") and 
      result = "CookieValue_PARAM") or
      (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestPart") and 
      result = "multipart/form-data_PARAM") or
      //test
     (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "PathVariable") and 
      result = "PATH_VARIABLE") or
     (a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "RequestBody") and 
     result = "BODY") 
     or
    // JAX-RS 注解检测
    (a.getType().hasQualifiedName("javax.ws.rs", "QueryParam") and 
    result = "QUERY_PARAM") or
    (a.getType().hasQualifiedName("javax.ws.rs", "PathParam") and 
    result = "PATH_VARIABLE")
}

string test11(Parameter p){
  if not exists(Annotation a | a = p.getAnAnnotation()) 
    then
      result = "不存在注解"
    else 
      exists(Annotation a |
        (a = p.getAnAnnotation() and not (
          // 排除校验类注解
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "NotNull") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "NotEmpty") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Size") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Pattern") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Min") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Max") or
          a.getType().hasQualifiedName("org.springframework.web.bind.annotation", "Valid") 
          )  and result = analyzePathParam_change_a(a)

        )
      )
}


// 获取参数的基础类型信息
string getParameterTypeInfo(Parameter p) {
  exists(RefType t | t = p.getType() |
    if isBasicType(t) 
    then result = t.getName() + "  传参方式：" +test11(p)
    else result = "复合类型[" + t.getName() + "传参方式:" +  test11(p)   + "  ]包含基础字段: " + 
    //t.getAField()  + 
    concat(string s | t.getAField().toString()=s  |s,"|" )
  )
}


// 2. 参数信息格式化谓词
string formatParameters(Method m){
  if m.getNumberOfParameters() > 0
  then result = getParameterTypeInfo(m.getAParameter())
  else result = "空参数"
}



// 4. 主查询：输出所有有效路径
from Class c, Method m, string fullPath, string httpMethods
where
  isSpringController(c) and              // 确认是 Controller 类
  m.getDeclaringType() = c and           // 方法属于该 Controller
  isSpringRequestMappingMethod(m) and    // 确认是映射方法
  fullPath = getFullWebPath(c, m) and    // 获取组合路径
  httpMethods = getHttpMethod(m)        // 获取 HTTP 方法
select m, c,fullPath,httpMethods,  formatParameters(m),
  "完整路径: " + fullPath +
  " | HTTP方法: " + httpMethods +
  " | 类: " + c.getQualifiedName() +
  " | 方法: " + m.getName()
